#!/usr/bin/env ts-node

import { AutomatedProofSystem } from "../../src/validator/AutomatedProofSystem";
import { VerificationContext } from "../../src/validator/InvariantVerifier";
import { Metrics } from "../../src/monitoring/metrics/Metrics";

/**
 * Demo script for Automated Proof Generation System
 * 
 * Demonstrates how to use the automated proof generation system
 * to generate proofs for new invariants.
 */

async function main() {
  console.log("=== Automated Proof Generation Demo ===\n");

  // Initialize the proof system
  const proofSystem = new AutomatedProofSystem({
    enableCaching: true,
    enableOptimization: true,
    enableComposition: true,
    confidenceThreshold: 0.7,
    maxProofSteps: 50
  });

  console.log("✓ Proof system initialized");
  console.log(`  Configuration: ${JSON.stringify(proofSystem.getConfig(), null, 2)}\n`);

  // Create verification context
  const context: VerificationContext = {
    moduleData: {
      name: "demo-module",
      version: "1.0.0",
      invariants: ["holographic_correspondence", "signature_binding", "throughput_bound"]
    },
    referenceFingerprint: undefined,
    performanceMetrics: new Metrics(),
    executionEnvironment: {
      nodeVersion: process.version,
      platform: process.platform,
      arch: process.arch
    }
  };

  // Demo 1: Analyze an invariant
  console.log("1. Analyzing invariant: holographic_correspondence");
  try {
    const analysis = await proofSystem.analyzeInvariant("holographic_correspondence", context);
    console.log(`   Category: ${analysis.category}`);
    console.log(`   Complexity: ${analysis.complexity}`);
    console.log(`   Strategy: ${analysis.proofStrategy.type} - ${analysis.proofStrategy.approach}`);
    console.log(`   Estimated Steps: ${analysis.estimatedSteps}`);
    console.log(`   Dependencies: ${analysis.dependencies.join(", ")}\n`);
  } catch (error) {
    console.error(`   Error: ${error instanceof Error ? error.message : String(error)}\n`);
  }

  // Demo 2: Generate proof for a single invariant
  console.log("2. Generating proof for: signature_binding");
  try {
    const result = await proofSystem.generateAndVerifyProof("signature_binding", context);
    
    if (result.success && result.proof && result.verification) {
      console.log(`   ✓ Proof generated successfully`);
      console.log(`   Artifact: ${result.proof.proofArtifact}`);
      console.log(`   Confidence: ${result.proof.confidence.toFixed(3)}`);
      console.log(`   Verification: ${result.verification.verified ? "PASS" : "FAIL"}`);
      console.log(`   Execution Time: ${result.executionTime}ms`);
      console.log(`   Strategy: ${result.proof.metadata.strategy.type}`);
      console.log(`   Steps: ${result.proof.proof.steps.length}\n`);
    } else {
      console.log(`   ✗ Proof generation failed: ${result.error}\n`);
    }
  } catch (error) {
    console.error(`   Error: ${error instanceof Error ? error.message : String(error)}\n`);
  }

  // Demo 3: Generate proofs for multiple invariants
  console.log("3. Generating proofs for multiple invariants");
  const invariants = ["holographic_correspondence", "throughput_bound"];
  try {
    const results = await proofSystem.generateProofsForInvariants(invariants, context);
    
    let successful = 0;
    let failed = 0;
    
    for (const result of results) {
      if (result.success) {
        successful++;
        console.log(`   ✓ ${result.proof!.invariant}: confidence ${result.proof!.confidence.toFixed(3)}`);
      } else {
        failed++;
        console.log(`   ✗ ${result.error}`);
      }
    }
    
    console.log(`   Summary: ${successful} successful, ${failed} failed\n`);
  } catch (error) {
    console.error(`   Error: ${error instanceof Error ? error.message : String(error)}\n`);
  }

  // Demo 4: Create a proof chain
  console.log("4. Creating proof chain: security_chain");
  try {
    const chain = await proofSystem.createProofChain(
      "security_chain",
      ["signature_binding", "holographic_correspondence"],
      context,
      "sequential"
    );
    
    if (chain) {
      console.log(`   ✓ Proof chain created: ${chain.id}`);
      console.log(`   Name: ${chain.name}`);
      console.log(`   Proofs: ${chain.proofs.length}`);
      console.log(`   Verification: ${chain.verificationResult ? "PASS" : "FAIL"}`);
      console.log(`   Confidence: ${chain.confidence.toFixed(3)}`);
      console.log(`   Complexity: ${chain.metadata.complexity}`);
      console.log(`   Total Steps: ${chain.metadata.totalSteps}\n`);
    } else {
      console.log(`   ✗ Proof chain creation failed\n`);
    }
  } catch (error) {
    console.error(`   Error: ${error instanceof Error ? error.message : String(error)}\n`);
  }

  // Demo 5: Validate all proofs
  console.log("5. Validating all generated proofs");
  try {
    const validation = await proofSystem.validateAllProofs();
    console.log(`   Total: ${validation.total}`);
    console.log(`   Valid: ${validation.valid}`);
    console.log(`   Invalid: ${validation.invalid}`);
    console.log(`   Success Rate: ${validation.total > 0 ? (validation.valid / validation.total * 100).toFixed(1) : 0}%\n`);
  } catch (error) {
    console.error(`   Error: ${error instanceof Error ? error.message : String(error)}\n`);
  }

  // Demo 6: Show system statistics
  console.log("6. System Statistics");
  const stats = proofSystem.getStats();
  console.log(`   Total Proofs: ${stats.totalProofs}`);
  console.log(`   Successful: ${stats.successfulProofs}`);
  console.log(`   Failed: ${stats.failedProofs}`);
  console.log(`   Average Confidence: ${stats.averageConfidence.toFixed(3)}`);
  console.log(`   Average Generation Time: ${stats.averageGenerationTime.toFixed(0)}ms`);
  console.log(`   Average Verification Time: ${stats.averageVerificationTime.toFixed(0)}ms`);
  console.log(`   Proof Chains: ${stats.proofChains}`);
  console.log(`   Total Steps: ${stats.totalSteps}\n`);

  // Demo 7: Generate system report
  console.log("7. System Report");
  const report = proofSystem.generateReport();
  console.log(report);

  console.log("\n=== Demo Completed ===");
}

// Run the demo
if (require.main === module) {
  main().catch(error => {
    console.error("Demo failed:", error);
    process.exit(1);
  });
}
