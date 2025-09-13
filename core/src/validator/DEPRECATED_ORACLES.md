# Deprecated Oracle Implementations

⚠️ **WARNING: These oracle implementations are deprecated and will be removed in a future version.**

## Deprecated Files

The following oracle implementations have been consolidated into the `MasterHologramOracle`:

- `src/validator/HologramOracle.ts` → Use `MasterHologramOracle` with mode `'base'`
- `src/validator/EnhancedHologramOracle.ts` → Use `MasterHologramOracle` with mode `'enhanced'`
- `src/validator/MLEnhancedHologramOracle.ts` → Use `MasterHologramOracle` with mode `'ml-enhanced'`
- `src/validator/StrictHolographicCoherenceOracle.ts` → Use `MasterHologramOracle` with mode `'strict'`
- `src/validator/DevelopmentOracle.ts` → Use `MasterHologramOracle` with mode `'development'`
- `src/validator/OracleMiddleware.ts` → Use `MasterHologramOracle` with mode `'middleware'`

## Deprecated CLI Tools

The following CLI tools have been consolidated into `master-oracle-cli.ts`:

- `src/validator/oracle-cli.ts` → Use `master-oracle-cli.ts --mode base`
- `src/validator/enhanced-oracle-cli.ts` → Use `master-oracle-cli.ts --mode enhanced`
- `src/validator/ml-enhanced-oracle-cli.ts` → Use `master-oracle-cli.ts --mode ml-enhanced`
- `src/validator/strict-oracle-cli.ts` → Use `master-oracle-cli.ts --mode strict`
- `src/validator/dev-oracle-cli.ts` → Use `master-oracle-cli.ts --mode development`

## Migration

Please see `docs/ORACLE_CONSOLIDATION_MIGRATION.md` for detailed migration instructions.

## Timeline

- **Current**: Deprecated implementations are still available but marked as deprecated
- **Next Release**: Deprecated implementations will show warnings when used
- **Future Release**: Deprecated implementations will be removed entirely

## Quick Migration Examples

### Old Code:
```typescript
import { HologramOracle } from './HologramOracle';
const oracle = new HologramOracle();
const result = oracle.validateModule('path/to/module.json');
```

### New Code:
```typescript
import { MasterHologramOracle } from './MasterHologramOracle';
const oracle = new MasterHologramOracle({ type: 'base', config: {} });
const result = await oracle.validate('path/to/module.json');
```

### Old CLI:
```bash
npm run validate:oracle:enhanced
```

### New CLI:
```bash
npm run oracle:enhanced --input modules/example.json
```

Please migrate to the new `MasterHologramOracle` as soon as possible to avoid future breaking changes.
