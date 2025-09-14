import json, sys
from pathlib import Path
p = Path("reports/e2e/events.jsonl")
if not p.exists():
    print("no events yet"); sys.exit(0)
counts = {}
last_for = {}
for line in p.read_text().splitlines():
    try:
        row = json.loads(line)
    except: 
        continue
    k = (row.get("suite"), row.get("event"))
    counts[k] = counts.get(k, 0) + 1
    last_for[k] = row
print("== counts ==")
for k,v in sorted(counts.items()):
    print(f"{k}: {v}")
print("\n== last events ==")
for k,row in sorted(last_for.items()):
    print(k, "→", {kk:row[kk] for kk in ("ts","cid","name","variant") if kk in row})
