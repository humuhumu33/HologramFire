import os, sys, requests

URL = os.getenv("GRAPHQL_URL")
if not URL:
    print("GRAPHQL_URL not set")
    sys.exit(2)

q = """
mutation($name:String!, $content:String!){
  upsertObject(name:$name, content:$content){ name }
}"""

name = os.getenv("GRAPHQL_TEST_NAME", "demo/object/alpha")
content = "Hello Hologram"
r = requests.post(URL, json={"query": q, "variables":{"name":name,"content":content}})
r.raise_for_status()
print("Seed result:", r.json())
