/**
 * Gate Verification and Stamping System
 * 
 * This module implements the gate verification system that maps operations
 * to specific gates and provides comprehensive audit trails for the HoloPost demo.
 * 
 * Based on the gate plan:
 * - Bootstrap: G0, G1, G3, G4, G5, G7
 * - Phase A (Transport): G6, G2, G1, G3, G4, G7
 * - Phase B (Storage): G5, G8, G1, G4
 * - Phase C (Compute): G7, G3, G1, G6, G8, G4, G0
 */

import { vpiRegistry } from '../runtime/vpi-registry';

export interface GateStamp {
  gate: string;
  family: string;
  spec: string;
  operation: string;
  timestamp: number;
  phase: 'bootstrap' | 'transport' | 'storage' | 'compute';
  details: {
    description: string;
    purpose: string;
    dependencies?: string[];
    outputs?: string[];
  };
}

export interface GateAuditTrail {
  phase: string;
  gates: GateStamp[];
  startTime: number;
  endTime?: number;
  totalGates: number;
  success: boolean;
}

/**
 * Gate definitions based on the specification
 */
export const GATE_DEFINITIONS = {
  // G0 - Hologram Oracle
  'G0.hologram-oracle.spec': {
    family: 'G0',
    spec: 'hologram-oracle.spec',
    description: 'Loads the blueprint/meta-module, fixed-point self-check',
    purpose: 'Bootstrap holographic coherence verification',
    phases: ['bootstrap', 'compute']
  },
  'G0.strict-holographic-coherence-oracle.spec': {
    family: 'G0',
    spec: 'strict-holographic-coherence-oracle.spec',
    description: 'Fail-closed init of invariants',
    purpose: 'Initialize strict coherence constraints',
    phases: ['bootstrap', 'compute']
  },

  // G1 - Core
  'G1.holography.spec': {
    family: 'G1',
    spec: 'holography.spec',
    description: 'Enables Φ bulk–boundary checks',
    purpose: 'Enable holographic boundary verification',
    phases: ['bootstrap', 'transport', 'storage', 'compute']
  },
  'G1.conservation.spec': {
    family: 'G1',
    spec: 'conservation.spec',
    description: 'Turns on budget-sum-to-zero invariant',
    purpose: 'Enforce budget conservation across operations',
    phases: ['bootstrap', 'transport', 'storage', 'compute']
  },
  'G1.resonance.spec': {
    family: 'G1',
    spec: 'resonance.spec',
    description: 'Activates R96/C768 lattice classes (48×256 layout policy)',
    purpose: 'Enable resonance-based placement and verification',
    phases: ['bootstrap', 'storage', 'compute']
  },

  // G2 - Klein
  'G2.klein.spec': {
    family: 'G2',
    spec: 'klein.spec',
    description: '192-probe on ingress (frame integrity)',
    purpose: 'Fast frame integrity verification',
    phases: ['transport']
  },

  // G3 - Logic
  'G3.r96.semiring.spec': {
    family: 'G3',
    spec: 'r96.semiring.spec',
    description: 'Budget algebra (add/sub/zero, closure rules)',
    purpose: 'Enable budget arithmetic and closure verification',
    phases: ['bootstrap', 'transport', 'storage', 'compute']
  },
  'G3.proof.composition.spec': {
    family: 'G3',
    spec: 'proof.composition.spec',
    description: 'Compositionality across steps/windows',
    purpose: 'Enable proof composition across operations',
    phases: ['bootstrap', 'transport', 'storage', 'compute']
  },

  // G4 - Crypto
  'G4.receipt.spec': {
    family: 'G4',
    spec: 'receipt.spec',
    description: 'Receipt schema + signature envelope',
    purpose: 'Generate and verify operation receipts',
    phases: ['bootstrap', 'transport', 'storage', 'compute', 'encoding']
  },
  'G4.holosig.spec': {
    family: 'G4',
    spec: 'holosig.spec',
    description: 'Holographic signature primitives',
    purpose: 'Enable holographic signature verification',
    phases: ['bootstrap', 'storage', 'encoding']
  },
  'G4.alpha.attestation.spec': {
    family: 'G4',
    spec: 'alpha.attestation.spec',
    description: 'Alpha attestation primitives',
    purpose: 'Enable alpha attestation verification',
    phases: ['bootstrap', 'storage', 'encoding']
  },
  'G4.ccm.kat.spec': {
    family: 'G4',
    spec: 'ccm.kat.spec',
    description: 'CCM KAT (Known Answer Test) primitives',
    purpose: 'Enable CCM verification primitives',
    phases: ['bootstrap', 'storage']
  },
  'G4.boundary.spec': {
    family: 'G4',
    spec: 'boundary.spec',
    description: 'Cross-boundary (host/region) proof format',
    purpose: 'Enable cross-boundary proof verification',
    phases: ['bootstrap', 'storage']
  },

  // G5 - Identity
  'G5.uorid.kat.spec': {
    family: 'G5',
    spec: 'uorid.kat.spec',
    description: 'UOR-ID derivation + deterministic placement seeds',
    purpose: 'Generate UOR-IDs and placement seeds',
    phases: ['bootstrap', 'storage']
  },
  'G5.fixtures.spec': {
    family: 'G5',
    spec: 'fixtures.spec',
    description: 'Deterministic placement fixtures',
    purpose: 'Provide deterministic placement data',
    phases: ['bootstrap', 'storage']
  },

  // G6 - Transport
  'G6.ctp.handshake.spec': {
    family: 'G6',
    spec: 'ctp.handshake.spec',
    description: 'Establish lane/window params + mutual auth',
    purpose: 'Establish CTP connection parameters',
    phases: ['transport']
  },
  'G6.ctp.fail.spec': {
    family: 'G6',
    spec: 'ctp.fail.spec',
    description: 'Immediate reject on over-budget / malformed frames',
    purpose: 'Handle transport failure conditions',
    phases: ['transport']
  },

  // G7 - Runtime
  'G7.vpi.registry.spec': {
    family: 'G7',
    spec: 'vpi.registry.spec',
    description: 'Kernel/driver registration (compute & IO shims)',
    purpose: 'Register and manage kernel execution',
    phases: ['bootstrap', 'compute']
  },
  'G7.local.verifier.spec': {
    family: 'G7',
    spec: 'local.verifier.spec',
    description: 'Fast-path local checks enabled',
    purpose: 'Enable local verification paths',
    phases: ['bootstrap', 'transport', 'storage', 'compute']
  },
  'G7.local.transport.spec': {
    family: 'G7',
    spec: 'local.transport.spec',
    description: 'Instrument & log window closure',
    purpose: 'Instrument and log transport operations',
    phases: ['bootstrap', 'transport']
  },

  // G8 - Persistence
  'G8.object.spec': {
    family: 'G8',
    spec: 'object.spec',
    description: 'Object layout & placement contract (tiles, EC/replicas)',
    purpose: 'Define object storage layout and placement',
    phases: ['storage']
  },
  'G8.ledger.spec': {
    family: 'G8',
    spec: 'ledger.spec',
    description: 'Record/verify the closed write window',
    purpose: 'Record and verify storage operations',
    phases: ['storage']
  }
};

/**
 * Gate verification manager
 */
export class GateVerifier {
  private auditTrails: Map<string, GateAuditTrail> = new Map();
  private currentPhase: string | null = null;

  /**
   * Start a new phase and initialize audit trail
   */
  startPhase(phase: string): void {
    this.currentPhase = phase;
    const auditTrail: GateAuditTrail = {
      phase,
      gates: [],
      startTime: Date.now(),
      totalGates: 0,
      success: false
    };
    this.auditTrails.set(phase, auditTrail);
    
    console.log(`\n🚀 Starting Phase: ${phase.toUpperCase()}`);
    console.log('─'.repeat(60));
  }

  /**
   * Stamp an operation with the appropriate gate
   */
  stampGate(gateKey: string, operation: string, details?: any): GateStamp {
    if (!this.currentPhase) {
      throw new Error('No active phase - call startPhase() first');
    }

    const gateDef = GATE_DEFINITIONS[gateKey as keyof typeof GATE_DEFINITIONS];
    if (!gateDef) {
      throw new Error(`Unknown gate: ${gateKey}`);
    }

    // Verify gate is appropriate for current phase
    if (!gateDef.phases.includes(this.currentPhase as any)) {
      console.warn(`⚠️  Gate ${gateKey} not typically used in phase ${this.currentPhase}`);
    }

    const stamp: GateStamp = {
      gate: gateKey,
      family: gateDef.family,
      spec: gateDef.spec,
      operation,
      timestamp: Date.now(),
      phase: this.currentPhase as any,
      details: {
        description: gateDef.description,
        purpose: gateDef.purpose,
        ...details
      }
    };

    // Add to audit trail
    const auditTrail = this.auditTrails.get(this.currentPhase);
    if (auditTrail) {
      auditTrail.gates.push(stamp);
      auditTrail.totalGates++;
    }

    // Log the gate usage
    this.logGateUsage(stamp);

    return stamp;
  }

  /**
   * Complete the current phase
   */
  completePhase(success: boolean = true): GateAuditTrail | null {
    if (!this.currentPhase) {
      return null;
    }

    const auditTrail = this.auditTrails.get(this.currentPhase);
    if (auditTrail) {
      auditTrail.endTime = Date.now();
      auditTrail.success = success;
    }

    this.logPhaseCompletion(auditTrail);
    this.currentPhase = null;

    return auditTrail || null;
  }

  /**
   * Get audit trail for a phase
   */
  getAuditTrail(phase: string): GateAuditTrail | undefined {
    return this.auditTrails.get(phase);
  }

  /**
   * Get all audit trails
   */
  getAllAuditTrails(): Map<string, GateAuditTrail> {
    return new Map(this.auditTrails);
  }

  /**
   * Log gate usage
   */
  private logGateUsage(stamp: GateStamp): void {
    console.log(`🔧 [${stamp.family}] ${stamp.spec}`);
    console.log(`   Operation: ${stamp.operation}`);
    console.log(`   Purpose: ${stamp.details.purpose}`);
    console.log(`   Description: ${stamp.details.description}`);
    if (stamp.details.dependencies) {
      console.log(`   Dependencies: ${stamp.details.dependencies.join(', ')}`);
    }
    if (stamp.details.outputs) {
      console.log(`   Outputs: ${stamp.details.outputs.join(', ')}`);
    }
    console.log(`   Timestamp: ${new Date(stamp.timestamp).toISOString()}`);
    console.log('');
  }

  /**
   * Log phase completion
   */
  private logPhaseCompletion(auditTrail: GateAuditTrail | undefined): void {
    if (!auditTrail) return;

    const duration = auditTrail.endTime ? auditTrail.endTime - auditTrail.startTime : 0;
    const status = auditTrail.success ? '✅ SUCCESS' : '❌ FAILED';
    
    console.log('\n' + '─'.repeat(60));
    console.log(`🎯 Phase ${auditTrail.phase.toUpperCase()} ${status}`);
    console.log(`   Duration: ${duration}ms`);
    console.log(`   Gates Used: ${auditTrail.totalGates}`);
    console.log(`   Gate Sequence:`);
    
    auditTrail.gates.forEach((gate, index) => {
      console.log(`     ${index + 1}. ${gate.family} - ${gate.operation}`);
    });
    
    console.log('─'.repeat(60));
  }

  /**
   * Generate comprehensive audit report
   */
  generateAuditReport(): string {
    let report = '\n' + '='.repeat(80);
    report += '\n🔍 HOLOGRAM GATE AUDIT REPORT';
    report += '\n' + '='.repeat(80);
    
    let totalGates = 0;
    let totalDuration = 0;
    
    for (const [phase, trail] of this.auditTrails) {
      const duration = trail.endTime ? trail.endTime - trail.startTime : 0;
      totalGates += trail.totalGates;
      totalDuration += duration;
      
      report += `\n\n📋 Phase: ${phase.toUpperCase()}`;
      report += `\n   Status: ${trail.success ? '✅ SUCCESS' : '❌ FAILED'}`;
      report += `\n   Duration: ${duration}ms`;
      report += `\n   Gates: ${trail.totalGates}`;
      report += `\n   Gate Sequence:`;
      
      trail.gates.forEach((gate, index) => {
        report += `\n     ${index + 1}. ${gate.gate} - ${gate.operation}`;
        report += `\n        Purpose: ${gate.details.purpose}`;
      });
    }
    
    report += `\n\n📊 SUMMARY:`;
    report += `\n   Total Phases: ${this.auditTrails.size}`;
    report += `\n   Total Gates: ${totalGates}`;
    report += `\n   Total Duration: ${totalDuration}ms`;
    report += `\n   Average Gates per Phase: ${(totalGates / this.auditTrails.size).toFixed(1)}`;
    
    report += '\n\n🎯 GATE FAMILY USAGE:';
    const familyUsage = new Map<string, number>();
    for (const trail of this.auditTrails.values()) {
      for (const gate of trail.gates) {
        familyUsage.set(gate.family, (familyUsage.get(gate.family) || 0) + 1);
      }
    }
    
    for (const [family, count] of familyUsage) {
      report += `\n   ${family}: ${count} uses`;
    }
    
    report += '\n' + '='.repeat(80);
    
    return report;
  }
}

/**
 * Global gate verifier instance
 */
export const gateVerifier = new GateVerifier();

/**
 * Convenience functions for common gate operations
 */
export const GateOps = {
  // Bootstrap gates
  bootstrap: {
    hologramOracle: (operation: string) => 
      gateVerifier.stampGate('G0.hologram-oracle.spec', operation),
    strictCoherence: (operation: string) => 
      gateVerifier.stampGate('G0.strict-holographic-coherence-oracle.spec', operation),
    holography: (operation: string) => 
      gateVerifier.stampGate('G1.holography.spec', operation),
    conservation: (operation: string) => 
      gateVerifier.stampGate('G1.conservation.spec', operation),
    resonance: (operation: string) => 
      gateVerifier.stampGate('G1.resonance.spec', operation),
    r96Semiring: (operation: string) => 
      gateVerifier.stampGate('G3.r96.semiring.spec', operation),
    proofComposition: (operation: string) => 
      gateVerifier.stampGate('G3.proof.composition.spec', operation),
    receipt: (operation: string) => 
      gateVerifier.stampGate('G4.receipt.spec', operation),
    holosig: (operation: string) => 
      gateVerifier.stampGate('G4.holosig.spec', operation),
    alphaAttestation: (operation: string) => 
      gateVerifier.stampGate('G4.alpha.attestation.spec', operation),
    ccmKat: (operation: string) => 
      gateVerifier.stampGate('G4.ccm.kat.spec', operation),
    boundary: (operation: string) => 
      gateVerifier.stampGate('G4.boundary.spec', operation),
    uoridKat: (operation: string) => 
      gateVerifier.stampGate('G5.uorid.kat.spec', operation),
    fixtures: (operation: string) => 
      gateVerifier.stampGate('G5.fixtures.spec', operation),
    vpiRegistry: (operation: string) => {
      vpiRegistry.initialize();
      return gateVerifier.stampGate('G7.vpi.registry.spec', operation);
    },
    localVerifier: (operation: string) => 
      gateVerifier.stampGate('G7.local.verifier.spec', operation),
    localTransport: (operation: string) => 
      gateVerifier.stampGate('G7.local.transport.spec', operation)
  },

  // Transport gates
  transport: {
    ctpHandshake: (operation: string) => 
      gateVerifier.stampGate('G6.ctp.handshake.spec', operation),
    klein: (operation: string) => 
      gateVerifier.stampGate('G2.klein.spec', operation),
    ctpFail: (operation: string) => 
      gateVerifier.stampGate('G6.ctp.fail.spec', operation)
  },

  // Storage gates
  storage: {
    object: (operation: string) => 
      gateVerifier.stampGate('G8.object.spec', operation),
    ledger: (operation: string) => 
      gateVerifier.stampGate('G8.ledger.spec', operation)
  }
};
