# Phase 5: GraphQL Named Content + Proof Chain

This phase tests GraphQL integration for named content resolution and proof chain validation against a real GraphQL server.

## Setup

1. **Set up your GraphQL server** with the following schema:
   ```graphql
   type Query {
     resolve(name: String!): ResolveResult
     inverseResolve(encoding: String!): InverseResolveResult
     verifyProof(name: String!, tamperedHash: String!): VerifyResult  # optional
   }
   
   type ResolveResult {
     encoding: String!
     proofChain: [ProofLayer]  # optional
   }
   
   type InverseResolveResult {
     name: String!
   }
   
   type ProofLayer {
     layer: String!
     hash: String!
     valid: Boolean!
   }
   
   type VerifyResult {
     valid: Boolean!
   }
   
   type Mutation {
     upsertObject(name: String!, content: String!): UpsertResult  # for seeding
   }
   
   type UpsertResult {
     name: String!
   }
   ```

2. **Set environment variables**:
   ```bash
   export GRAPHQL_URL=http://localhost:4000/graphql
   export GRAPHQL_TEST_NAME=demo/object/alpha  # optional, defaults to demo/object/alpha
   ```

3. **Seed test data** (if needed):
   ```bash
   python scripts/seed_graphql_demo.py
   ```

## Running Tests

```bash
# Run all Phase 5 tests
python -m pytest -m phase5_graphql -v

# Run specific test files
python -m pytest tests/phase5_graphql/test_graphql_resolution.py -v
python -m pytest tests/phase5_graphql/test_graphql_negatives.py -v
```

## Test Coverage

- **Name to encoding resolution** with optional proof chain validation
- **Inverse bijection** (encoding back to name)
- **Error handling** for non-existent names
- **Proof tampering detection** (if server supports verification)

## Notes

- Tests **skip automatically** if `GRAPHQL_URL` is not set
- Server can implement proof chain gradually - tests pass without it initially
- Proof verification endpoint is optional but recommended for security
- Adjust `TEST_NAME` and error cases to match your server's data model
