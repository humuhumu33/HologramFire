import json

# Try a list of candidate GraphQL ops until one works, else raise the last error.
def try_graphql(client, variants, variables):
    errs = []
    for title, q in variants:
        try:
            data = client.query(q, variables)
            return title, data
        except Exception as e:
            errs.append(f"{title}: {e}")
    raise RuntimeError("All GraphQL variants failed:\n" + "\n".join(errs))

def pretty(obj): return json.dumps(obj, indent=2, sort_keys=True)
