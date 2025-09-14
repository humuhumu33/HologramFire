import csv, os, statistics as stats, time
from pathlib import Path

def pct(arr, p):
    if not arr: return None
    i = max(0, min(len(arr)-1, int(len(arr)*p) - 1))
    return sorted(arr)[i]

def measure(fn, *args, warmup=10, runs=50):
    # warmup
    for _ in range(warmup): fn(*args)
    # timed
    samples=[]
    for _ in range(runs):
        t0 = time.perf_counter()
        fn(*args)
        samples.append((time.perf_counter()-t0)*1000.0)  # ms
    return {
        "p50": pct(samples, 0.50),
        "p95": pct(samples, 0.95),
        "p99": pct(samples, 0.99),
        "avg": sum(samples)/len(samples),
        "n": len(samples),
        "samples": samples,
    }

def write_csv(rows, fname):
    out = Path("reports/perf"); out.mkdir(parents=True, exist_ok=True)
    path = out / fname
    new = not path.exists()
    with open(path, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["suite","metric","p50_ms","p95_ms","p99_ms","avg_ms","n","note"])
        for r in rows:
            w.writerow(r)
    return str(path)
