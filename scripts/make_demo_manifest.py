import json, os, time, hashlib, sys
from pathlib import Path

def main(out="demo.manifest.json", name=None):
    name = name or os.getenv("E2E_APP_NAME","demo/app/hello")
    manifest = {
        "schema": "https://hologram.foundation/schemas/service",
        "name": name,
        "version": "1.0.0",
        "created": int(time.time()),
        "entrypoints": {"default": "main"},
        "permissions": ["read:user"],
        "meta": {"kind":"demo","phase":"8"}
    }
    blob = json.dumps(manifest, separators=(",",":")).encode()
    sha = hashlib.sha256(blob).hexdigest()
    manifest["sha256"] = sha
    Path(out).write_text(json.dumps(manifest, indent=2))
    print(out)
if __name__ == "__main__":
    main(*(sys.argv[1:] or []))
