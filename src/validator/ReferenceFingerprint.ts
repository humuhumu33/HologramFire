import { ccmHash } from "../crypto/ccm/CCMHash";
import { Metrics } from "../monitoring/metrics/Metrics";

export interface ReferenceFingerprintData {
  moduleId: string;
  invariants: string[];
  implementation: any;
  timestamp: string;
  version: string;
}

export interface ReferenceFingerprint {
  digest: string;
  timestamp: string;
  version: string;
  python_hash: string;
  execution_witness: string;
  holographic_correspondence: string;
}

export interface FingerprintResult {
  fingerprint: string;
  isValid: boolean;
  confidence: number;
  details: string;
}

export class DynamicReferenceFingerprint {
  private metrics: Metrics;
  private fingerprints: Map<string, string> = new Map();

  constructor() {
    this.metrics = new Metrics();
  }

  generateFingerprint(data: ReferenceFingerprintData): string {
    const startTime = Date.now();
    
    try {
      // Create a stable representation of the data
      const stableData = this.createStableRepresentation(data);
      
      // Generate CCM hash as fingerprint
      const fingerprint = ccmHash(stableData, "reference.fingerprint");
      
      // Store the fingerprint
      this.fingerprints.set(data.moduleId, fingerprint);
      
      const executionTime = Date.now() - startTime;
      this.metrics.observe("fingerprint_generation_time_ms", executionTime);
      this.metrics.inc("fingerprints_generated", 1);
      
      return fingerprint;
      
    } catch (error) {
      this.metrics.inc("fingerprint_generation_errors", 1);
      throw new Error(`Fingerprint generation failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  validateFingerprint(moduleId: string, expectedFingerprint: string): FingerprintResult {
    const startTime = Date.now();
    
    try {
      const storedFingerprint = this.fingerprints.get(moduleId);
      
      if (!storedFingerprint) {
        return {
          fingerprint: "",
          isValid: false,
          confidence: 0,
          details: "No stored fingerprint found for module"
        };
      }
      
      const isValid = storedFingerprint === expectedFingerprint;
      const confidence = isValid ? 1.0 : 0.0;
      
      const executionTime = Date.now() - startTime;
      this.metrics.observe("fingerprint_validation_time_ms", executionTime);
      this.metrics.inc("fingerprints_validated", 1);
      
      return {
        fingerprint: storedFingerprint,
        isValid,
        confidence,
        details: isValid ? "Fingerprint matches" : "Fingerprint mismatch"
      };
      
    } catch (error) {
      this.metrics.inc("fingerprint_validation_errors", 1);
      return {
        fingerprint: "",
        isValid: false,
        confidence: 0,
        details: `Validation error: ${error instanceof Error ? error.message : String(error)}`
      };
    }
  }

  private createStableRepresentation(data: ReferenceFingerprintData): any {
    // Create a stable, deterministic representation of the data
    return {
      moduleId: data.moduleId,
      invariants: data.invariants.sort(), // Sort for consistency
      implementation: this.normalizeImplementation(data.implementation),
      timestamp: data.timestamp,
      version: data.version
    };
  }

  private normalizeImplementation(implementation: any): any {
    // Normalize implementation data for consistent fingerprinting
    if (typeof implementation === "string") {
      return implementation.trim();
    }
    
    if (typeof implementation === "object" && implementation !== null) {
      // Sort object keys for consistency
      const sorted: any = {};
      Object.keys(implementation).sort().forEach(key => {
        sorted[key] = this.normalizeImplementation(implementation[key]);
      });
      return sorted;
    }
    
    return implementation;
  }

  getStoredFingerprint(moduleId: string): string | undefined {
    return this.fingerprints.get(moduleId);
  }

  clearFingerprint(moduleId: string): boolean {
    return this.fingerprints.delete(moduleId);
  }

  getAllFingerprints(): Map<string, string> {
    return new Map(this.fingerprints);
  }

  generateReferenceFingerprint(): ReferenceFingerprint {
    const timestamp = new Date().toISOString();
    const digest = ccmHash({ timestamp }, "reference.fingerprint");
    
    return {
      digest,
      timestamp,
      version: '1.0.0',
      python_hash: ccmHash({ timestamp, type: 'python' }, "reference.python"),
      execution_witness: ccmHash({ timestamp, type: 'witness' }, "reference.witness"),
      holographic_correspondence: ccmHash({ timestamp, type: 'correspondence' }, "reference.correspondence")
    };
  }
}