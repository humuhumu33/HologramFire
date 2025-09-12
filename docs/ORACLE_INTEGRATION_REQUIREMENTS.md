# Oracle Integration Requirements

## Overview

All new hologram and data functions **MUST** be validated against the hologram_generator_mini oracle to ensure coherence. This document outlines the mandatory requirements and processes for maintaining system coherence.

## 🚨 **MANDATORY REQUIREMENTS**

### 1. **All New Code Must Pass Oracle Validation**

Every new hologram or data function must achieve an **oracle score of 0.95 or higher** before being committed to the codebase.

### 2. **Required Oracle Patterns**

All new functions must include at least one of the following patterns:

#### **Holographic Correspondence Patterns:**
- `holographic`
- `correspondence` 
- `oracle`
- `coherence`
- `fingerprint`
- `invariant`

#### **Resonance Classification Patterns:**
- `resonance`
- `frequency`
- `harmonic`
- `oscillation`
- `vibration`

#### **Cycle Conservation Patterns:**
- `cycle`
- `conservation`
- `energy`
- `efficiency`
- `optimization`

#### **Page Conservation Patterns:**
- `page`
- `memory`
- `storage`
- `allocation`
- `management`

### 3. **Data Function Requirements**

Data functions must additionally include:
- `validation`
- `integrity`
- `consistency`
- `checksum`
- `hash`
- `verify`

## 🔧 **Integration Methods**

### **Method 1: Pre-commit Hook (Recommended)**

The oracle validation runs automatically before every commit:

```bash
# Install the pre-commit hook
npm run pre-commit:oracle
```

This will:
- ✅ Validate all staged files
- ✅ Check oracle compliance
- ✅ Block commits with oracle score < 0.95
- ✅ Provide detailed violation reports

### **Method 2: Real-time Development Validation**

Use the development oracle for real-time feedback:

```bash
# Start development oracle
npm run dev:oracle
```

This provides:
- 🔍 Real-time validation as you type
- 💡 Instant suggestions for improvements
- 📊 Live oracle score updates
- 🚨 Immediate violation alerts

### **Method 3: Manual Validation**

Validate specific files manually:

```bash
# Validate a module
npm run validate:oracle modules/your-module.json

# Validate a blueprint
npm run validate:oracle:blueprint atlas-12288/blueprint/blueprint.json

# Validate all files
npm run validate:oracle:all
```

## 📋 **Code Examples**

### ✅ **Good Hologram Function**

```typescript
/**
 * Holographic data processor with oracle validation
 */
export function processHolographicData(data: any): ProcessedData {
  // Holographic correspondence pattern ✓
  const holographicFingerprint = generateFingerprint(data);
  
  // Resonance classification pattern ✓
  const resonanceFrequency = analyzeResonance(data);
  
  // Cycle conservation pattern ✓
  const energyEfficiency = optimizeCycles(data);
  
  // Page conservation pattern ✓
  const memoryAllocation = managePages(data);
  
  // Oracle validation
  const oracleResult = validateWithOracle(data);
  if (!oracleResult.ok) {
    throw new Error(`Oracle validation failed: ${oracleResult.violations}`);
  }
  
  return {
    fingerprint: holographicFingerprint,
    resonance: resonanceFrequency,
    efficiency: energyEfficiency,
    memory: memoryAllocation
  };
}
```

### ✅ **Good Data Function**

```typescript
/**
 * Data integrity validator with holographic correspondence
 */
export function validateDataIntegrity(data: any): ValidationResult {
  // Data integrity patterns ✓
  const checksum = calculateChecksum(data);
  const hash = generateHash(data);
  
  // Holographic correspondence pattern ✓
  const holographicCorrespondence = verifyCorrespondence(data);
  
  // Oracle validation
  const oracleResult = validateWithOracle(data);
  if (!oracleResult.ok) {
    throw new Error(`Oracle validation failed: ${oracleResult.violations}`);
  }
  
  return {
    valid: true,
    checksum,
    hash,
    correspondence: holographicCorrespondence
  };
}
```

### ❌ **Bad Function (Will Fail Oracle)**

```typescript
// Missing all required patterns
export function badFunction(data: any): any {
  // No holographic patterns
  // No resonance patterns  
  // No cycle conservation
  // No page conservation
  // No oracle validation
  
  return data; // This will fail oracle validation
}
```

## 🚫 **Common Violations**

### **Critical Violations (Score = 0)**
- Missing holographic correspondence patterns
- No oracle validation calls
- Missing data integrity patterns

### **Warning Violations (Score = 0.9)**
- Missing resonance classification
- Missing cycle conservation
- Missing page conservation

### **Info Violations (Score = 0.95)**
- Suboptimal holographic structure
- Missing best practice patterns

## 🔍 **Validation Process**

### **Step 1: Code Analysis**
The oracle analyzes your code for:
- Pattern recognition
- Structure validation
- Coherence scoring
- Violation detection

### **Step 2: Scoring**
- **1.0**: Perfect oracle compliance
- **0.95+**: Acceptable for production
- **0.8-0.94**: Requires review and fixes
- **<0.8**: Critical violations, must be fixed

### **Step 3: Feedback**
The oracle provides:
- Detailed violation reports
- Specific improvement suggestions
- Quick fix recommendations
- Best practice guidance

## 🛠️ **Development Workflow**

### **1. Write Code**
```typescript
export function myNewFunction(data: any) {
  // Your code here
}
```

### **2. Real-time Validation**
The development oracle automatically validates and provides feedback:
```
⚠️ Code has minor oracle violations (87.5%)
💡 Add holographic correspondence patterns
💡 Include resonance classification
```

### **3. Apply Suggestions**
```typescript
export function myNewFunction(data: any) {
  // Holographic correspondence ✓
  const holographicFingerprint = generateFingerprint(data);
  
  // Resonance classification ✓
  const resonance = analyzeResonance(data);
  
  // Oracle validation ✓
  const oracleResult = validateWithOracle(data);
  
  return { fingerprint: holographicFingerprint, resonance };
}
```

### **4. Pre-commit Validation**
```bash
git add .
git commit -m "Add new hologram function"
# Oracle validation runs automatically
# ✅ All oracle validations passed. Proceeding with commit.
```

## 📊 **Monitoring and Reporting**

### **Compliance Reports**
```bash
# Get compliance report for a directory
npm run dev:oracle --report src/
```

### **Statistics**
```bash
# Get oracle validation statistics
npm run dev:oracle --stats
```

## 🚨 **Enforcement**

### **Automatic Enforcement**
- Pre-commit hooks block non-compliant code
- CI/CD pipeline validates all changes
- Development tools provide real-time feedback

### **Manual Enforcement**
- Code reviews must include oracle validation
- All PRs must pass oracle checks
- Production deployments require oracle compliance

## 📚 **Best Practices**

1. **Always include oracle validation calls** in your functions
2. **Use holographic patterns** throughout your code
3. **Maintain resonance classification** for all hologram functions
4. **Implement cycle conservation** for efficiency
5. **Apply page conservation** for memory management
6. **Validate data integrity** for all data functions
7. **Follow the oracle suggestions** for improvements

## 🔗 **Related Documentation**

- [Hologram Oracle Process](./HOLOGRAM_ORACLE_PROCESS.md)
- [Oracle API Reference](./ORACLE_API_REFERENCE.md)
- [Troubleshooting Guide](./ORACLE_TROUBLESHOOTING.md)

---

**Remember: The oracle is the source of truth for system coherence. All new code must maintain holographic correspondence with hologram_generator_mini.**
