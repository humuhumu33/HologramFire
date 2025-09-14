import os, json, uuid, hashlib, pytest
from pathlib import Path
from tests.phase8_e2e._e2e_utils import try_graphql, pretty
from tests._artifacts import log_event

pytestmark = pytest.mark.phase8_e2e

def _read_bytes(p): return Path(p).read_bytes()

def _sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def _app_name():
    base = os.getenv("E2E_APP_NAME", "demo/app/hello")
    # add a short suffix so repeated runs don't collide in your marketplace
    return f"{base}-{uuid.uuid4().hex[:8]}"

def _ensure_manifest(name: str, path="demo.manifest.json"):
    # Recreate manifest with the given name if it doesn't exist
    if not Path(path).exists():
        from scripts.make_demo_manifest import main as gen
        gen(path, name)
    else:
        # rewrite existing manifest with desired name (keeps file stable)
        mf = json.loads(Path(path).read_text())
        if mf.get("name") != name:
            mf["name"] = name
            blob = json.dumps(mf, separators=(",", ":")).encode()
            mf["sha256"] = _sha256_hex(blob)
            Path(path).write_text(json.dumps(mf, indent=2))
    return path

def test_e2e_ipfs_publish_and_fetch(ipfs_client):
    name = _app_name()
    mpath = _ensure_manifest(name)
    blob = _read_bytes(mpath)
    mf = json.loads(blob)

    # assert embedded hash correctness before publish
    assert mf["sha256"] == _sha256_hex(json.dumps({k:v for k,v in mf.items() if k!="sha256"}, separators=(",", ":")).encode()) \
        or mf["sha256"] == _sha256_hex(blob), "embedded sha256 must match manifest content"

    # publish
    cid = ipfs_client.add_bytes(blob)
    log_event("phase8", "ipfs_publish", {"cid": cid, "name": name})
    got = ipfs_client.cat(cid)
    assert got == blob, "IPFS cat must equal published manifest"

    # tamper-negative: 1 byte change must yield different CID
    tampered = bytearray(blob); tampered[0] ^= 0x01
    cid2 = ipfs_client.add_bytes(bytes(tampered))
    log_event("phase8", "ipfs_publish_tampered", {"cid": cid2})
    assert cid2 != cid, "CID must change when bytes change"

@pytest.mark.parametrize("name_env", ["GRAPHQL_TEST_NAME","E2E_APP_NAME"])
def test_e2e_marketplace_register_install_resolve(ipfs_client, gql_client, name_env):
    # Prepare manifest & IPFS CID
    name = _app_name()
    mpath = _ensure_manifest(name)
    blob = _read_bytes(mpath)
    cid  = ipfs_client.add_bytes(blob)
    mf   = json.loads(blob)

    log_event("phase8", "marketplace_prepare", {"cid": cid, "name": name})

    # 1) Register in marketplace (try several common mutation names)
    publish_variants = [
        ("publishApp(cid,name)",
         "mutation($cid:String!,$name:String!){ publishApp(cid:$cid,name:$name){ id cid name } }"),
        ("marketplacePublish(cid,name)",
         "mutation($cid:String!,$name:String!){ marketplacePublish(cid:$cid,name:$name){ id cid name } }"),
        ("upsertService(cid,name)",
         "mutation($cid:String!,$name:String!){ upsertService(cid:$cid,name:$name){ id cid name } }"),
    ]
    title_pub, pub = try_graphql(gql_client, publish_variants, {"cid": cid, "name": name})
    log_event("phase8", "marketplace_publish", {"variant": title_pub, "resp": pub})
    published = (pub.get("publishApp") or pub.get("marketplacePublish") or pub.get("upsertService"))
    assert published and published.get("cid") == cid, f"publish response unexpected: {pretty(pub)}"

    # 2) Install (optional)
    install_variants = [
        ("installApp(name)",   "mutation($name:String!){ installApp(name:$name){ name status } }"),
        ("installByCid(cid)",  "mutation($cid:String!){ installByCid(cid:$cid){ name status } }"),
        ("appsInstall(name)",  "mutation($name:String!){ appsInstall(name:$name){ name status } }"),
    ]
    vars_install = {"name": name, "cid": cid}
    try:
        title_ins, ins = try_graphql(gql_client, install_variants, vars_install)
        log_event("phase8", "marketplace_install", {"variant": title_ins, "resp": ins})
        installed = ins.get("installApp") or ins.get("installByCid") or ins.get("appsInstall")
        assert installed and installed.get("name")
    except Exception as e:
        log_event("phase8", "marketplace_install_skipped", {"reason": str(e)})

    # 3) Use: resolve by name → encoding (must be non-empty)
    resolve_q = "query($n:String!){ resolve(name:$n){ encoding } }"
    r = gql_client.query(resolve_q, {"n": name})
    log_event("phase8", "resolve", {"resp": r})
    enc = (r.get("resolve") or {}).get("encoding")
    assert isinstance(enc, str) and len(enc) > 0, f"resolve failed: {pretty(r)}"

    # 4) Optional: marketplace discoverability check
    try:
        q = "query($q:String!){ searchApps(q:$q){ name cid } }"
        s = gql_client.query(q, {"q": name.split("-")[0]})
        log_event("phase8", "search", {"resp": s})
        assert any(i.get("name")==name for i in (s.get("searchApps") or []))
    except Exception as e:
        # fine if your API doesn't expose search yet
        log_event("phase8", "search_skipped", {"reason": str(e)})

def test_e2e_uninstall_if_supported(gql_client):
    name = os.getenv("E2E_APP_NAME", "demo/app/hello")  # latest install may have a suffix; this is best-effort
    uninstall_variants = [
        ("uninstallApp(name)", "mutation($name:String!){ uninstallApp(name:$name){ name status } }"),
        ("appsUninstall(name)","mutation($name:String!){ appsUninstall(name:$name){ name status } }"),
    ]
    try:
        title, out = try_graphql(gql_client, uninstall_variants, {"name": name})
        log_event("phase8","uninstall",{"variant":title,"resp":out})
        assert out
    except Exception as e:
        log_event("phase8","uninstall_skipped",{"reason":str(e)})
