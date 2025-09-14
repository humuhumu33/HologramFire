import csv, json, html, sys
from pathlib import Path
from collections import defaultdict

PERF_DIR = Path("reports/perf")
E2E_DIR  = Path("reports/e2e")
OUT      = Path("reports/index.html")

def read_perf():
    rows = []
    for p in PERF_DIR.glob("*.csv"):
        with p.open(newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            rows += [{**row, "_file": p.name} for row in r]
    return rows

def read_e2e():
    events = []
    f = E2E_DIR / "events.jsonl"
    if f.exists():
        for line in f.read_text(encoding="utf-8").splitlines():
            try: events.append(json.loads(line))
            except: pass
    return events

def table(headers, rows):
    th = "".join(f"<th>{html.escape(h)}</th>" for h in headers)
    trs=[]
    for row in rows:
        tds = []
        for h in headers:
            val = row.get(h, "")
            if isinstance(val, (dict, list)):
                val = json.dumps(val, separators=(",",":"))
            tds.append(f"<td>{html.escape(str(val))}</td>")
        trs.append("<tr>" + "".join(tds) + "</tr>")
    return f"<table><thead><tr>{th}</tr></thead><tbody>{''.join(trs)}</tbody></table>"

def main():
    OUT.parent.mkdir(parents=True, exist_ok=True)

    perf = read_perf()
    e2e  = read_e2e()

    # Perf quick summary (best row per metric by p95_ms)
    best = {}
    for row in perf:
        key = (row["suite"], row["metric"])
        p95 = float(row.get("p95_ms") or 0)
        if key not in best or p95 < float(best[key].get("p95_ms") or 1e9):
            best[key] = row
    best_rows = [dict(suite=k[0], metric=k[1], **{kk: vv for kk, vv in v.items() if kk not in ['suite', 'metric']}) for k,v in best.items()]

    # E2E counts
    counts = defaultdict(int)
    last   = {}
    for ev in e2e:
        k = (ev.get("suite"), ev.get("event"))
        counts[k]+=1
        last[k] = ev

    html_doc = f"""<!doctype html>
<html>
<head>
<meta charset="utf-8"/>
<title>Hologram Reports</title>
<style>
  body{{font-family:system-ui,Segoe UI,Roboto,Arial,sans-serif;padding:20px;}}
  h2{{margin-top:28px}}
  table{{border-collapse:collapse;width:100%;margin:10px 0}}
  th,td{{border:1px solid #ddd;padding:8px;font-size:14px;vertical-align:top}}
  th{{background:#f6f7f9;text-align:left}}
  code,pre{{background:#f6f7f9;border:1px solid #e5e7eb;border-radius:6px;padding:3px 6px}}
  .grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:12px}}
  .card{{border:1px solid #e5e7eb;border-radius:10px;padding:12px}}
</style>
</head>
<body>
<h1>Hologram – Reports</h1>

<div class="grid">
  <div class="card">
    <h3>Perf CSV files</h3>
    <p>{html.escape(", ".join(sorted(set(r["_file"] for r in perf)) or ["(none)"]))}</p>
  </div>
  <div class="card">
    <h3>E2E events</h3>
    <p>{len(e2e)} total events</p>
  </div>
</div>

<h2>Perf – Best p95 per metric</h2>
{table(["suite","metric","p50_ms","p95_ms","p99_ms","avg_ms","n","_file","note"], best_rows)}

<h2>Perf – All rows</h2>
{table(["suite","metric","p50_ms","p95_ms","p99_ms","avg_ms","n","_file","note"], perf)}

<h2>E2E – Event counts</h2>
{table(["suite","event","count"], [{"suite":k[0],"event":k[1],"count":v} for k,v in sorted(counts.items())])}

<h2>E2E – Last events (per type)</h2>
{table(["suite","event","ts","cid","name","variant"], [
  {"suite":k[0],"event":k[1],"ts":v.get("ts"),"cid":v.get("cid"),"name":v.get("name"),"variant":v.get("variant")}
  for k,v in sorted(last.items())
])}

<h2>E2E – Raw events (latest 50)</h2>
<pre>{html.escape("\\n".join(json.dumps(e) for e in e2e[-50:]))}</pre>

</body>
</html>"""
    OUT.write_text(html_doc, encoding="utf-8")
    print(f"Wrote {OUT}")

if __name__ == "__main__":
    main()
