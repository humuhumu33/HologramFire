import os, pytest, time
from tests.phase6_perf._perf_utils import measure, write_csv

pytestmark = pytest.mark.phase6_perf

GQL_P95_MS   = float(os.getenv("SLO_GQL_P95_MS", "100"))  # default 100ms
SAMPLES      = int(os.getenv("GQL_SAMPLES", "40"))
WARMUP       = int(os.getenv("GQL_WARMUP", "5"))
TEST_NAME    = os.getenv("GRAPHQL_TEST_NAME", "demo/object/alpha")

def _resolve_once(gql_client, name):
    q = """
    query($n:String!){
      resolve(name:$n){ encoding }
    }"""
    data = gql_client.query(q, {"n": name})
    enc = data["resolve"]["encoding"]
    assert isinstance(enc, str) and len(enc) > 0
    return enc

def test_graphql_resolve_p95_under_slo(gql_client):
    # Warm up & measure using the same production endpoint
    # (retries and caches—if any—are part of prod behavior)
    stats = measure(lambda: _resolve_once(gql_client, TEST_NAME),
                    warmup=WARMUP, runs=SAMPLES)
    csv = write_csv([["graphql","resolve_ms", f"{stats['p50']:.3f}", f"{stats['p95']:.3f}",
                      f"{stats['p99']:.3f}", f"{stats['avg']:.3f}", stats["n"], f"name={TEST_NAME}"]],
                    "graphql_perf.csv")
    assert stats["p95"] < GQL_P95_MS, (
        f"GraphQL resolve p95={stats['p95']:.2f}ms exceeds {GQL_P95_MS}ms (CSV: {csv})"
    )
