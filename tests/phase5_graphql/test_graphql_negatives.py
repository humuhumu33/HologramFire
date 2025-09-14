import pytest

pytestmark = pytest.mark.phase5_graphql

def test_bad_name_rejected(gql_client):
    bad = "does/not/exist/"  # adjust to a name your server will reject
    q = "query($n:String!){ resolve(name:$n){ encoding } }"
    # Server may throw GraphQL error or return null — support both
    try:
        res = gql_client.query(q, {"n": bad})
        assert res["resolve"] is None or res["resolve"].get("encoding") in (None, "")
    except RuntimeError as e:
        # acceptable: GraphQL error
        assert "errors" in str(e) or "GraphQL errors" in str(e)

def test_tampered_proof_is_invalid_if_supported(gql_client):
    # Only run if server exposes proofChain with 'hash' + 'valid'
    q = """
    query($n:String!){
      resolve(name:$n){ encoding proofChain { layer hash valid } }
    }"""
    name = "demo/object/alpha"
    data = gql_client.query(q, {"n": name})
    pc = (data.get("resolve") or {}).get("proofChain") or []
    if not pc or "hash" not in pc[0]:
        pytest.skip("Server does not provide proof hashes; skipping tamper test.")
    # tamper: flip last char of first hash
    h = pc[0]["hash"]
    bad_hash = (h[:-1] + ("0" if h[-1] != "0" else "1")) if h else "00"
    # If your server has a verification endpoint/mutation, call it here. Otherwise,
    # define a verification query if available. For now, we assert the server marks invalid if rechecked.
    # Example optional query:
    qv = """
    query($n:String!, $h:String!){
      verifyProof(name:$n, tamperedHash:$h){ valid }
    }"""
    try:
        res = gql_client.query(qv, {"n": name, "h": bad_hash})
        assert res["verifyProof"]["valid"] is False
    except RuntimeError:
        pytest.skip("Proof verification endpoint not available; skipping negative proof test.")
