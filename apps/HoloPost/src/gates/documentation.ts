/**
 * Gate Documentation and Explanation System
 * 
 * This module provides comprehensive documentation and explanations for the
 * Hologram gate system used in the HoloPost demo. It makes it easy for
 * anyone running the demo to understand what gates are being used and how
 * they work.
 */

export interface GateExplanation {
  gate: string;
  family: string;
  spec: string;
  purpose: string;
  description: string;
  whenUsed: string[];
  dependencies: string[];
  outputs: string[];
  examples: string[];
  technicalDetails: {
    algorithm?: string;
    complexity?: string;
    security?: string;
    performance?: string;
  };
}

/**
 * Comprehensive gate explanations
 */
export const GATE_EXPLANATIONS: Record<string, GateExplanation> = {
  'G0.hologram-oracle.spec': {
    gate: 'G0.hologram-oracle.spec',
    family: 'G0',
    spec: 'hologram-oracle.spec',
    purpose: 'Bootstrap holographic coherence verification',
    description: 'Loads the blueprint/meta-module and performs fixed-point self-check to ensure the holographic system is in a coherent state.',
    whenUsed: ['Bootstrap phase', 'Compute phase completion'],
    dependencies: [],
    outputs: ['Holographic coherence state', 'Blueprint validation'],
    examples: [
      'Initialize holographic oracle at system startup',
      'Verify final conformance snapshot after compute operations'
    ],
    technicalDetails: {
      algorithm: 'Fixed-point iteration with holographic constraints',
      complexity: 'O(log n) where n is the number of holographic elements',
      security: 'Ensures no holographic violations can occur',
      performance: 'Fast initialization, minimal runtime overhead'
    }
  },

  'G0.strict-holographic-coherence-oracle.spec': {
    gate: 'G0.strict-holographic-coherence-oracle.spec',
    family: 'G0',
    spec: 'strict-holographic-coherence-oracle.spec',
    purpose: 'Initialize strict coherence constraints',
    description: 'Fail-closed initialization of invariants that must be maintained throughout the system lifecycle.',
    whenUsed: ['Bootstrap phase', 'Compute phase completion'],
    dependencies: ['G0.hologram-oracle.spec'],
    outputs: ['Strict coherence invariants', 'Fail-closed state'],
    examples: [
      'Initialize strict coherence constraints at startup',
      'Final verification of strict coherence after operations'
    ],
    technicalDetails: {
      algorithm: 'Invariant checking with fail-closed semantics',
      complexity: 'O(1) for invariant checks',
      security: 'Fail-closed ensures system safety',
      performance: 'Minimal overhead, critical for safety'
    }
  },

  'G1.holography.spec': {
    gate: 'G1.holography.spec',
    family: 'G1',
    spec: 'holography.spec',
    purpose: 'Enable holographic boundary verification',
    description: 'Enables Φ (phi) bulk–boundary checks that ensure holographic properties are maintained across system boundaries.',
    whenUsed: ['Bootstrap phase', 'All operational phases'],
    dependencies: ['G0.hologram-oracle.spec'],
    outputs: ['Holographic boundary state', 'Φ verification results'],
    examples: [
      'Enable holographic checks at system startup',
      'Verify holographic properties during transport',
      'Ensure holographic integrity during storage operations'
    ],
    technicalDetails: {
      algorithm: 'Φ bulk-boundary verification algorithm',
      complexity: 'O(b) where b is the number of boundaries',
      security: 'Prevents holographic boundary violations',
      performance: 'Efficient boundary checking'
    }
  },

  'G1.conservation.spec': {
    gate: 'G1.conservation.spec',
    family: 'G1',
    spec: 'conservation.spec',
    purpose: 'Enforce budget conservation across operations',
    description: 'Turns on budget-sum-to-zero invariant that ensures all budget operations are properly balanced.',
    whenUsed: ['Bootstrap phase', 'All operational phases'],
    dependencies: ['G3.r96.semiring.spec'],
    outputs: ['Budget conservation state', 'Conservation verification'],
    examples: [
      'Enable budget conservation at startup',
      'Verify budget balance during transport',
      'Ensure budget conservation during storage',
      'Validate budget conservation during compute'
    ],
    technicalDetails: {
      algorithm: 'Budget sum-to-zero invariant checking',
      complexity: 'O(1) for budget operations',
      security: 'Prevents budget leaks and attacks',
      performance: 'Minimal overhead, critical for correctness'
    }
  },

  'G1.resonance.spec': {
    gate: 'G1.resonance.spec',
    family: 'G1',
    spec: 'resonance.spec',
    purpose: 'Enable resonance-based placement and verification',
    description: 'Activates R96/C768 lattice classes with 48×256 layout policy for optimal placement and fault tolerance.',
    whenUsed: ['Bootstrap phase', 'Storage phase', 'Compute phase'],
    dependencies: ['G5.uorid.kat.spec'],
    outputs: ['Resonance classes', 'Placement policy'],
    examples: [
      'Activate resonance classes at startup',
      'Choose fault domains for storage placement',
      'Enable resonance-based compute pinning'
    ],
    technicalDetails: {
      algorithm: 'R96/C768 resonance class computation',
      complexity: 'O(1) for placement decisions',
      security: 'Ensures fault domain separation',
      performance: 'Fast placement decisions'
    }
  },

  'G2.klein.spec': {
    gate: 'G2.klein.spec',
    family: 'G2',
    spec: 'klein.spec',
    purpose: 'Fast frame integrity verification',
    description: '192-probe verification on ingress that provides fast frame integrity checking for transport operations.',
    whenUsed: ['Transport phase'],
    dependencies: ['G6.ctp.handshake.spec'],
    outputs: ['Frame integrity verification', 'Probe results'],
    examples: [
      'Verify frame integrity during transport',
      'Fast rejection of malformed frames'
    ],
    technicalDetails: {
      algorithm: '192-probe Klein verification',
      complexity: 'O(1) constant time verification',
      security: 'High confidence frame integrity',
      performance: 'Ultra-fast verification, critical for transport'
    }
  },

  'G3.r96.semiring.spec': {
    gate: 'G3.r96.semiring.spec',
    family: 'G3',
    spec: 'r96.semiring.spec',
    purpose: 'Enable budget arithmetic and closure verification',
    description: 'Provides budget algebra with add/sub/zero operations and closure rules for all budget operations.',
    whenUsed: ['Bootstrap phase', 'All operational phases'],
    dependencies: [],
    outputs: ['Budget algebra operations', 'Closure verification'],
    examples: [
      'Enable budget arithmetic at startup',
      'Validate budget operations during transport',
      'Ensure budget closure during storage',
      'Verify budget algebra during compute'
    ],
    technicalDetails: {
      algorithm: 'Semiring algebra with closure properties',
      complexity: 'O(1) for budget operations',
      security: 'Mathematical guarantees for budget operations',
      performance: 'Efficient budget arithmetic'
    }
  },

  'G3.proof.composition.spec': {
    gate: 'G3.proof.composition.spec',
    family: 'G3',
    spec: 'proof.composition.spec',
    purpose: 'Enable proof composition across operations',
    description: 'Enables compositionality across steps and windows, allowing proofs to be combined and verified together.',
    whenUsed: ['Bootstrap phase', 'All operational phases'],
    dependencies: ['G4.receipt.spec'],
    outputs: ['Composed proofs', 'Composition verification'],
    examples: [
      'Enable proof composition at startup',
      'Compose proofs across transport windows',
      'Combine proofs for storage operations',
      'Aggregate proofs for compute operations'
    ],
    technicalDetails: {
      algorithm: 'Proof composition with associativity',
      complexity: 'O(k) where k is the number of composed proofs',
      security: 'Maintains proof integrity across composition',
      performance: 'Efficient proof combination'
    }
  },

  'G4.receipt.spec': {
    gate: 'G4.receipt.spec',
    family: 'G4',
    spec: 'receipt.spec',
    purpose: 'Generate and verify operation receipts',
    description: 'Provides receipt schema and signature envelope for all operations, ensuring verifiable audit trails.',
    whenUsed: ['Bootstrap phase', 'All operational phases'],
    dependencies: ['G4.holosig.spec'],
    outputs: ['Operation receipts', 'Signature envelopes'],
    examples: [
      'Generate receipts for transport settlement',
      'Create receipts for storage operations',
      'Produce receipts for compute operations',
      'Verify receipt signatures'
    ],
    technicalDetails: {
      algorithm: 'Receipt generation with cryptographic signatures',
      complexity: 'O(1) for receipt generation',
      security: 'Cryptographically secure receipts',
      performance: 'Fast receipt generation and verification'
    }
  },

  'G4.holosig.spec': {
    gate: 'G4.holosig.spec',
    family: 'G4',
    spec: 'holosig.spec',
    purpose: 'Enable holographic signature verification',
    description: 'Provides holographic signature primitives for secure witness verification and attestation.',
    whenUsed: ['Bootstrap phase', 'Storage phase'],
    dependencies: [],
    outputs: ['Holographic signatures', 'Signature verification'],
    examples: [
      'Initialize holographic signatures at startup',
      'Sign storage witnesses',
      'Verify holographic signatures'
    ],
    technicalDetails: {
      algorithm: 'Holographic signature scheme',
      complexity: 'O(1) for signature operations',
      security: 'Quantum-resistant holographic signatures',
      performance: 'Efficient signature generation and verification'
    }
  },

  'G4.alpha.attestation.spec': {
    gate: 'G4.alpha.attestation.spec',
    family: 'G4',
    spec: 'alpha.attestation.spec',
    purpose: 'Enable alpha attestation verification',
    description: 'Provides alpha attestation primitives for secure witness verification and integrity checking.',
    whenUsed: ['Bootstrap phase', 'Storage phase'],
    dependencies: ['G4.holosig.spec'],
    outputs: ['Alpha attestations', 'Attestation verification'],
    examples: [
      'Initialize alpha attestation at startup',
      'Create alpha attestations for witnesses',
      'Verify alpha attestations'
    ],
    technicalDetails: {
      algorithm: 'Alpha attestation protocol',
      complexity: 'O(1) for attestation operations',
      security: 'High-confidence attestation verification',
      performance: 'Fast attestation generation and verification'
    }
  },

  'G4.ccm.kat.spec': {
    gate: 'G4.ccm.kat.spec',
    family: 'G4',
    spec: 'ccm.kat.spec',
    purpose: 'Enable CCM verification primitives',
    description: 'Provides CCM (Counter with CBC-MAC) KAT (Known Answer Test) primitives for cryptographic verification.',
    whenUsed: ['Bootstrap phase', 'Storage phase'],
    dependencies: [],
    outputs: ['CCM verification results', 'KAT test results'],
    examples: [
      'Initialize CCM KAT primitives at startup',
      'Perform CCM verification for storage',
      'Run KAT tests for cryptographic validation'
    ],
    technicalDetails: {
      algorithm: 'CCM with Known Answer Tests',
      complexity: 'O(1) for CCM operations',
      security: 'Cryptographically secure CCM verification',
      performance: 'Efficient CCM operations'
    }
  },

  'G4.boundary.spec': {
    gate: 'G4.boundary.spec',
    family: 'G4',
    spec: 'boundary.spec',
    purpose: 'Enable cross-boundary proof verification',
    description: 'Provides cross-boundary (host/region) proof format for secure operations across system boundaries.',
    whenUsed: ['Bootstrap phase', 'Storage phase'],
    dependencies: ['G1.holography.spec'],
    outputs: ['Cross-boundary proofs', 'Boundary verification'],
    examples: [
      'Initialize cross-boundary proofs at startup',
      'Create proofs for cross-region storage',
      'Verify cross-boundary proofs for repair'
    ],
    technicalDetails: {
      algorithm: 'Cross-boundary proof protocol',
      complexity: 'O(b) where b is the number of boundaries',
      security: 'Secure cross-boundary operations',
      performance: 'Efficient boundary proof generation'
    }
  },

  'G5.uorid.kat.spec': {
    gate: 'G5.uorid.kat.spec',
    family: 'G5',
    spec: 'uorid.kat.spec',
    purpose: 'Generate UOR-IDs and placement seeds',
    description: 'Provides UOR-ID derivation and deterministic placement seeds for consistent object placement.',
    whenUsed: ['Bootstrap phase', 'Storage phase'],
    dependencies: [],
    outputs: ['UOR-IDs', 'Placement seeds'],
    examples: [
      'Initialize UOR-ID derivation at startup',
      'Generate UOR-IDs for postcard objects',
      'Create deterministic placement seeds'
    ],
    technicalDetails: {
      algorithm: 'Content-addressed UOR-ID generation',
      complexity: 'O(1) for UOR-ID generation',
      security: 'Deterministic and collision-resistant',
      performance: 'Fast UOR-ID generation'
    }
  },

  'G5.fixtures.spec': {
    gate: 'G5.fixtures.spec',
    family: 'G5',
    spec: 'fixtures.spec',
    purpose: 'Provide deterministic placement data',
    description: 'Provides deterministic placement fixtures for consistent and reproducible object placement.',
    whenUsed: ['Bootstrap phase', 'Storage phase'],
    dependencies: ['G5.uorid.kat.spec'],
    outputs: ['Placement fixtures', 'Deterministic data'],
    examples: [
      'Load placement fixtures at startup',
      'Use fixtures for deterministic placement',
      'Ensure reproducible placement decisions'
    ],
    technicalDetails: {
      algorithm: 'Deterministic fixture generation',
      complexity: 'O(1) for fixture access',
      security: 'Deterministic and predictable',
      performance: 'Fast fixture access'
    }
  },

  'G6.ctp.handshake.spec': {
    gate: 'G6.ctp.handshake.spec',
    family: 'G6',
    spec: 'ctp.handshake.spec',
    purpose: 'Establish CTP connection parameters',
    description: 'Establishes lane/window parameters and mutual authentication for the Consensus Transport Protocol.',
    whenUsed: ['Transport phase'],
    dependencies: [],
    outputs: ['CTP connection state', 'Authentication results'],
    examples: [
      'Establish CTP handshake for transport',
      'Set up lane and window parameters',
      'Perform mutual authentication'
    ],
    technicalDetails: {
      algorithm: 'CTP handshake protocol',
      complexity: 'O(1) for handshake operations',
      security: 'Mutual authentication and parameter validation',
      performance: 'Fast handshake establishment'
    }
  },

  'G6.ctp.fail.spec': {
    gate: 'G6.ctp.fail.spec',
    family: 'G6',
    spec: 'ctp.fail.spec',
    purpose: 'Handle transport failure conditions',
    description: 'Provides immediate rejection on over-budget or malformed frames to maintain transport integrity.',
    whenUsed: ['Transport phase'],
    dependencies: ['G6.ctp.handshake.spec'],
    outputs: ['Failure responses', 'Rejection reasons'],
    examples: [
      'Reject over-budget transport requests',
      'Immediately reject malformed frames',
      'Handle transport failure conditions'
    ],
    technicalDetails: {
      algorithm: 'Fast failure detection and rejection',
      complexity: 'O(1) for failure detection',
      security: 'Prevents resource exhaustion attacks',
      performance: 'Immediate failure response'
    }
  },

  'G7.vpi.registry.spec': {
    gate: 'G7.vpi.registry.spec',
    family: 'G7',
    spec: 'vpi.registry.spec',
    purpose: 'Register and manage kernel execution',
    description: 'Provides kernel/driver registration for compute and IO shims, enabling kernel execution management.',
    whenUsed: ['Bootstrap phase', 'Compute phase'],
    dependencies: [],
    outputs: ['Kernel registry', 'Driver registration'],
    examples: [
      'Register kernel drivers at startup',
      'Spawn kernels for compute operations',
      'Manage kernel execution lifecycle'
    ],
    technicalDetails: {
      algorithm: 'Kernel registry and management',
      complexity: 'O(1) for kernel operations',
      security: 'Secure kernel execution environment',
      performance: 'Efficient kernel management'
    }
  },

  'G7.local.verifier.spec': {
    gate: 'G7.local.verifier.spec',
    family: 'G7',
    spec: 'local.verifier.spec',
    purpose: 'Enable local verification paths',
    description: 'Enables fast-path local checks for efficient verification without network overhead.',
    whenUsed: ['Bootstrap phase', 'All operational phases'],
    dependencies: [],
    outputs: ['Local verification state', 'Fast-path results'],
    examples: [
      'Enable local verification at startup',
      'Perform fast local checks during transport',
      'Use local verification for storage',
      'Enable local verification for compute'
    ],
    technicalDetails: {
      algorithm: 'Local verification with fast-path optimization',
      complexity: 'O(1) for local operations',
      security: 'Local verification with integrity guarantees',
      performance: 'Ultra-fast local verification'
    }
  },

  'G7.local.transport.spec': {
    gate: 'G7.local.transport.spec',
    family: 'G7',
    spec: 'local.transport.spec',
    purpose: 'Instrument and log transport operations',
    description: 'Provides instrumentation and logging for window closure and transport operations.',
    whenUsed: ['Bootstrap phase', 'Transport phase'],
    dependencies: ['G6.ctp.handshake.spec'],
    outputs: ['Transport instrumentation', 'Logging data'],
    examples: [
      'Enable transport instrumentation at startup',
      'Instrument window closure operations',
      'Log transport operation details'
    ],
    technicalDetails: {
      algorithm: 'Transport instrumentation and logging',
      complexity: 'O(1) for instrumentation operations',
      security: 'Secure logging and instrumentation',
      performance: 'Minimal overhead instrumentation'
    }
  },

  'G8.object.spec': {
    gate: 'G8.object.spec',
    family: 'G8',
    spec: 'object.spec',
    purpose: 'Define object storage layout and placement',
    description: 'Provides object layout and placement contract with tiles, erasure coding, and replica management.',
    whenUsed: ['Storage phase'],
    dependencies: ['G1.resonance.spec'],
    outputs: ['Object layout', 'Placement contracts'],
    examples: [
      'Define object layout for storage',
      'Create placement contracts with EC/replicas',
      'Manage object tiles and placement'
    ],
    technicalDetails: {
      algorithm: 'Object layout with erasure coding and replication',
      complexity: 'O(k+m) where k is data shards, m is parity shards',
      security: 'Fault-tolerant object storage',
      performance: 'Efficient object placement and retrieval'
    }
  },

  'G8.ledger.spec': {
    gate: 'G8.ledger.spec',
    family: 'G8',
    spec: 'ledger.spec',
    purpose: 'Record and verify storage operations',
    description: 'Records and verifies closed write windows for storage operations, providing audit trails.',
    whenUsed: ['Storage phase'],
    dependencies: ['G4.receipt.spec'],
    outputs: ['Storage ledger entries', 'Verification results'],
    examples: [
      'Record storage write windows',
      'Verify closed write operations',
      'Maintain storage audit trails'
    ],
    technicalDetails: {
      algorithm: 'Storage ledger with verification',
      complexity: 'O(1) for ledger operations',
      security: 'Tamper-evident storage ledger',
      performance: 'Efficient ledger operations'
    }
  }
};

/**
 * Get explanation for a specific gate
 */
export function getGateExplanation(gateKey: string): GateExplanation | undefined {
  return GATE_EXPLANATIONS[gateKey];
}

/**
 * Get all gates for a specific family
 */
export function getGatesByFamily(family: string): GateExplanation[] {
  return Object.values(GATE_EXPLANATIONS).filter(gate => gate.family === family);
}

/**
 * Get all gates used in a specific phase
 */
export function getGatesByPhase(phase: string): GateExplanation[] {
  return Object.values(GATE_EXPLANATIONS).filter(gate => 
    gate.whenUsed.some(usage => usage.toLowerCase().includes(phase.toLowerCase()))
  );
}

/**
 * Generate comprehensive gate documentation
 */
export function generateGateDocumentation(): string {
  let doc = '\n' + '='.repeat(80);
  doc += '\n📚 HOLOGRAM GATE DOCUMENTATION';
  doc += '\n' + '='.repeat(80);
  
  // Group by family
  const families = ['G0', 'G1', 'G2', 'G3', 'G4', 'G5', 'G6', 'G7', 'G8'];
  
  for (const family of families) {
    const familyGates = getGatesByFamily(family);
    if (familyGates.length === 0) continue;
    
    doc += `\n\n## ${family} - ${getFamilyDescription(family)}`;
    doc += '\n' + '-'.repeat(60);
    
    for (const gate of familyGates) {
      doc += `\n\n### ${gate.gate}`;
      doc += `\n**Purpose:** ${gate.purpose}`;
      doc += `\n**Description:** ${gate.description}`;
      doc += `\n**When Used:** ${gate.whenUsed.join(', ')}`;
      
      if (gate.dependencies.length > 0) {
        doc += `\n**Dependencies:** ${gate.dependencies.join(', ')}`;
      }
      
      if (gate.outputs.length > 0) {
        doc += `\n**Outputs:** ${gate.outputs.join(', ')}`;
      }
      
      doc += `\n**Examples:**`;
      for (const example of gate.examples) {
        doc += `\n  - ${example}`;
      }
      
      if (gate.technicalDetails.algorithm) {
        doc += `\n**Algorithm:** ${gate.technicalDetails.algorithm}`;
      }
      if (gate.technicalDetails.complexity) {
        doc += `\n**Complexity:** ${gate.technicalDetails.complexity}`;
      }
      if (gate.technicalDetails.security) {
        doc += `\n**Security:** ${gate.technicalDetails.security}`;
      }
      if (gate.technicalDetails.performance) {
        doc += `\n**Performance:** ${gate.technicalDetails.performance}`;
      }
    }
  }
  
  doc += '\n\n' + '='.repeat(80);
  doc += '\n🎯 GATE USAGE SUMMARY';
  doc += '\n' + '='.repeat(80);
  
  doc += '\n\n### Phase-by-Phase Gate Usage:';
  
  const phases = ['Bootstrap', 'Transport', 'Storage', 'Compute'];
  for (const phase of phases) {
    const phaseGates = getGatesByPhase(phase);
    doc += `\n\n**${phase} Phase:**`;
    for (const gate of phaseGates) {
      doc += `\n  - ${gate.gate}: ${gate.purpose}`;
    }
  }
  
  doc += '\n\n### Gate Family Overview:';
  for (const family of families) {
    const familyGates = getGatesByFamily(family);
    if (familyGates.length > 0) {
      doc += `\n  - **${family}**: ${familyGates.length} gates - ${getFamilyDescription(family)}`;
    }
  }
  
  doc += '\n' + '='.repeat(80);
  
  return doc;
}

/**
 * Get family description
 */
function getFamilyDescription(family: string): string {
  const descriptions: Record<string, string> = {
    'G0': 'Hologram Oracle - Core holographic verification and coherence',
    'G1': 'Core - Fundamental holographic operations and constraints',
    'G2': 'Klein - Fast frame integrity verification',
    'G3': 'Logic - Budget algebra and proof composition',
    'G4': 'Crypto - Cryptographic primitives and receipts',
    'G5': 'Identity - UOR-ID generation and placement',
    'G6': 'Transport - Consensus Transport Protocol',
    'G7': 'Runtime - Kernel management and local verification',
    'G8': 'Persistence - Object storage and ledger management'
  };
  
  return descriptions[family] || 'Unknown family';
}

/**
 * Generate quick reference guide
 */
export function generateQuickReference(): string {
  let ref = '\n' + '='.repeat(60);
  ref += '\n🚀 HOLOGRAM GATE QUICK REFERENCE';
  ref += '\n' + '='.repeat(60);
  
  ref += '\n\n### Bootstrap Phase (Startup):';
  ref += '\n  G0.hologram-oracle.spec → Initialize holographic oracle';
  ref += '\n  G0.strict-holographic-coherence-oracle.spec → Initialize strict coherence';
  ref += '\n  G1.holography.spec → Enable Φ bulk–boundary checks';
  ref += '\n  G1.conservation.spec → Enable budget-sum-to-zero invariant';
  ref += '\n  G1.resonance.spec → Activate R96/C768 lattice classes';
  ref += '\n  G3.r96.semiring.spec → Enable budget algebra';
  ref += '\n  G3.proof.composition.spec → Enable proof composition';
  ref += '\n  G4.receipt.spec → Initialize receipt schema';
  ref += '\n  G4.holosig.spec → Initialize holographic signatures';
  ref += '\n  G4.alpha.attestation.spec → Initialize alpha attestation';
  ref += '\n  G4.ccm.kat.spec → Initialize CCM KAT primitives';
  ref += '\n  G4.boundary.spec → Initialize cross-boundary proofs';
  ref += '\n  G5.uorid.kat.spec → Initialize UOR-ID derivation';
  ref += '\n  G5.fixtures.spec → Load deterministic placement fixtures';
  ref += '\n  G7.vpi.registry.spec → Register kernel/driver registry';
  ref += '\n  G7.local.verifier.spec → Enable local verification paths';
  ref += '\n  G7.local.transport.spec → Enable transport instrumentation';
  
  ref += '\n\n### Transport Phase (A→B, lane 2, O(1) verify):';
  ref += '\n  G6.ctp.handshake.spec → Establish lane/window params + mutual auth';
  ref += '\n  G2.klein.spec → 192-probe on ingress (frame integrity)';
  ref += '\n  G1.conservation.spec + G3.r96.semiring.spec → Budget window closure';
  ref += '\n  G4.receipt.spec → Emit settlement receipt for the window';
  ref += '\n  G6.ctp.fail.spec → Immediate reject on over-budget/malformed frames';
  ref += '\n  G7.local.transport.spec → Instrument & log window closure';
  
  ref += '\n\n### Storage Phase (PUT/GET/repair on 12,288 lattice):';
  ref += '\n  G5.uorid.kat.spec → Compute UOR-ID for the postcard';
  ref += '\n  G8.object.spec → Object layout & placement contract (tiles, EC/replicas)';
  ref += '\n  G1.resonance.spec → Choose rows/columns across distinct R96 classes';
  ref += '\n  G1.conservation.spec → Enforce write admission by budget';
  ref += '\n  G4.receipt.spec → PUT receipt (witness attached)';
  ref += '\n  G8.ledger.spec → Record/verify the closed write window';
  ref += '\n  G8.object.spec + G4.boundary.spec → Repair across rows/lanes with proof';
  ref += '\n  G4.receipt.spec → REPAIR receipt confirms closure';
  
  ref += '\n\n### Compute Phase (stamp kernel pinned near data):';
  ref += '\n  G7.vpi.registry.spec → Spawn kernel; scheduler pin "near: UOR-ID"';
  ref += '\n  G3.r96.semiring.spec + G1.conservation.spec → Preflight budget check';
  ref += '\n  G6 (transport) + G8 (persistence) → I/O operations (reused)';
  ref += '\n  G4.receipt.spec → COMPUTE receipt (per-kernel)';
  ref += '\n  G4.receipt.spec → Aggregate end-to-end window receipt';
  ref += '\n  G0.hologram-oracle.spec → Final conformance snapshot passes';
  ref += '\n  G0.strict-holographic-coherence-oracle.spec → Final coherence verification';
  
  ref += '\n\n' + '='.repeat(60);
  
  return ref;
}
