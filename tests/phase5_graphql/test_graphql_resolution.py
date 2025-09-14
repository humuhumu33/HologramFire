import os, pytest

pytestmark = pytest.mark.phase5_graphql

# change these names to a real object your server knows how to resolve
TEST_NAME = os.getenv("GRAPHQL_TEST_NAME", "demo/object/alpha")

def test_name_to_encoding_with_proofs(gql_client):
    q = """
    query($n:String!){
      resolve(name:$n){
        encoding
        proofChain { layer hash valid }
      }
    }"""
    data = gql_client.query(q, {"n": TEST_NAME})
    assert data and data.get("resolve"), "resolve() returned nothing"
    enc = data["resolve"]["encoding"]
    proofs = data["resolve"]["proofChain"] or []
    assert isinstance(enc, str) and len(enc) > 0
    # accept servers without proofChain initially, but prefer validation if present
    if proofs:
        assert all(p.get("valid") is True for p in proofs), f"invalid proof(s): {proofs}"

def test_inverse_bijection(gql_client):
    q1 = """
    query($n:String!){
      resolve(name:$n){ encoding }
    }"""
    q2 = """
    query($e:String!){
      inverseResolve(encoding:$e){ name }
    }"""
    r1 = gql_client.query(q1, {"n": TEST_NAME})
    enc = r1["resolve"]["encoding"]
    r2 = gql_client.query(q2, {"e": enc})
    assert r2["inverseResolve"]["name"] == TEST_NAME, "inverseResolve must return original name"
