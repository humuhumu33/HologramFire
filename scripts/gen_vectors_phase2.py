import sys
from pathlib import Path
sys.path.append(str(Path(__file__).parent.parent))
from tests._helpers import bridge_call

OUT = Path("vectors/bhic_cef"); OUT.mkdir(parents=True, exist_ok=True)

def main():
    data = b"Vectors CEF sample payload"
    cef_hex = bridge_call("cef:encode_hex", data.hex())["cefHex"]
    dec = bridge_call("cef:decode", cef_hex)
    (OUT / "sample.cef.hex").write_text(cef_hex)
    (OUT / "sample.meta.json").write_text(__import__("json").dumps(dec, indent=2))
    print("✓ wrote vectors/bhic_cef/sample.cef.hex and sample.meta.json")

if __name__ == "__main__":
    main()