#!/usr/bin/env ts-node

import { Command } from "commander";
import { AutomatedProofGenerator } from "./AutomatedProofGenerator";
import { EnhancedProofVerifier } from "./EnhancedProofVerifier";
import { InvariantAnalyzer } from "./InvariantAnalyzer";
import { ProofComposer } from "./ProofComposer";
import { Metrics } from "../monitoring/metrics/Metrics";
import { VerificationContext } from "./InvariantVerifier";
import fs from "node:fs";
import path from "node:path";

/**
 * CLI for Automated Proof Generation
 * 
 * Provides command-line interface for generating, verifying,
 * and managing automated proofs for new invariants.
 */

const program = new Command();
const metrics = new Metrics();

// Initialize components
const proofGenerator = new AutomatedProofGenerator(metrics);
const proofVerifier = new EnhancedProofVerifier(metrics);
const invariantAnalyzer = new InvariantAnalyzer(metrics);
const proofComposer = new ProofComposer(metrics);

program
  .name("automated-proof-cli")
  .description("CLI for automated proof generation for new invariants")
  .version("1.0.0");

// Generate proof for a single invariant
program
  .command("generate")
  .description("Generate proof for a single invariant")
  .argument("<invariant>", "The invariant to generate proof for")
  .option("-m, --module <path>", "Path to module file")
  .option("-o, --output <path>", "Output directory for generated proof")
  .option("-v, --verbose", "Verbose output")
  .action(async (invariant: string, options: any) => {
    try {
      console.log(`Generating proof for invariant: ${invariant}`);
      
      // Load module data if provided
      let moduleData = {};
      if (options.module) {
        if (!fs.existsSync(options.module)) {
          console.error(`Module file not found: ${options.module}`);
          process.exit(1);
        }
        moduleData = JSON.parse(fs.readFileSync(options.module, "utf8"));
      }
      
      // Create verification context
      const context: VerificationContext = {
        moduleData,
        referenceFingerprint: undefined,
        performanceMetrics: metrics,
        executionEnvironment: {
          nodeVersion: process.version,
          platform: process.platform,
          arch: process.arch
        }
      };
      
      // Generate proof
      const generatedProof = await proofGenerator.generateProofForInvariant(invariant, context);
      
      // Output results
      if (options.verbose) {
        console.log("\nGenerated Proof Details:");
        console.log(`  Invariant: ${generatedProof.invariant}`);
        console.log(`  Proof Artifact: ${generatedProof.proofArtifact}`);
        console.log(`  Digest: ${generatedProof.digest}`);
        console.log(`  Verification Result: ${generatedProof.verificationResult}`);
        console.log(`  Confidence: ${generatedProof.confidence.toFixed(3)}`);
        console.log(`  Strategy: ${generatedProof.metadata.strategy.type} - ${generatedProof.metadata.strategy.approach}`);
        console.log(`  Complexity: ${generatedProof.metadata.complexity}`);
        console.log(`  Steps: ${generatedProof.metadata.verificationSteps}`);
        console.log(`  Dependencies: ${generatedProof.metadata.dependencies.join(", ")}`);
      } else {
        console.log(`✓ Proof generated successfully`);
        console.log(`  Artifact: ${generatedProof.proofArtifact}`);
        console.log(`  Confidence: ${generatedProof.confidence.toFixed(3)}`);
      }
      
      // Save to output directory if specified
      if (options.output) {
        const outputDir = path.resolve(options.output);
        if (!fs.existsSync(outputDir)) {
          fs.mkdirSync(outputDir, { recursive: true });
        }
        
        const outputFile = path.join(outputDir, `${invariant}_proof.json`);
        fs.writeFileSync(outputFile, JSON.stringify(generatedProof, null, 2));
        console.log(`  Saved to: ${outputFile}`);
      }
      
    } catch (error) {
      console.error(`Error generating proof: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// Verify a generated proof
program
  .command("verify")
  .description("Verify a generated proof")
  .argument("<proof-path>", "Path to generated proof file")
  .option("-v, --verbose", "Verbose output")
  .action(async (proofPath: string, options: any) => {
    try {
      console.log(`Verifying proof: ${proofPath}`);
      
      if (!fs.existsSync(proofPath)) {
        console.error(`Proof file not found: ${proofPath}`);
        process.exit(1);
      }
      
      // Load proof
      const proof = JSON.parse(fs.readFileSync(proofPath, "utf8"));
      
      // Verify proof
      const verificationResult = await proofVerifier.verifyGeneratedProof(proof);
      
      // Output results
      if (options.verbose) {
        console.log("\nVerification Results:");
        console.log(`  Verified: ${verificationResult.verified ? "PASS" : "FAIL"}`);
        console.log(`  Confidence: ${verificationResult.confidence.toFixed(3)}`);
        console.log(`  Method: ${verificationResult.verificationMethod}`);
        console.log(`  Execution Time: ${verificationResult.executionTime}ms`);
        
        console.log("\nEvidence:");
        console.log(`  Structural: ${verificationResult.evidence.structuralValid ? "PASS" : "FAIL"}`);
        console.log(`  Artifact: ${verificationResult.evidence.artifactValid ? "PASS" : "FAIL"}`);
        console.log(`  Mathematical: ${verificationResult.evidence.mathematicalValid ? "PASS" : "FAIL"}`);
        console.log(`  Cryptographic: ${verificationResult.evidence.cryptographicValid ? "PASS" : "FAIL"}`);
        console.log(`  Computational: ${verificationResult.evidence.computationalValid ? "PASS" : "FAIL"}`);
        console.log(`  Dependencies: ${verificationResult.evidence.dependenciesValid ? "PASS" : "FAIL"}`);
        console.log(`  Digest: ${verificationResult.evidence.digestValid ? "PASS" : "FAIL"}`);
        
        console.log("\nRecommendations:");
        verificationResult.recommendations.forEach(rec => console.log(`  - ${rec}`));
      } else {
        console.log(`✓ Verification ${verificationResult.verified ? "PASSED" : "FAILED"}`);
        console.log(`  Confidence: ${verificationResult.confidence.toFixed(3)}`);
        if (!verificationResult.verified) {
          console.log(`  Issues: ${verificationResult.recommendations.length}`);
        }
      }
      
    } catch (error) {
      console.error(`Error verifying proof: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// Analyze an invariant
program
  .command("analyze")
  .description("Analyze an invariant to determine proof strategy")
  .argument("<invariant>", "The invariant to analyze")
  .option("-m, --module <path>", "Path to module file")
  .option("-v, --verbose", "Verbose output")
  .action(async (invariant: string, options: any) => {
    try {
      console.log(`Analyzing invariant: ${invariant}`);
      
      // Load module data if provided
      let moduleData = {};
      if (options.module) {
        if (!fs.existsSync(options.module)) {
          console.error(`Module file not found: ${options.module}`);
          process.exit(1);
        }
        moduleData = JSON.parse(fs.readFileSync(options.module, "utf8"));
      }
      
      // Create verification context
      const context: VerificationContext = {
        moduleData,
        referenceFingerprint: undefined,
        performanceMetrics: metrics,
        executionEnvironment: {
          nodeVersion: process.version,
          platform: process.platform,
          arch: process.arch
        }
      };
      
      // Analyze invariant
      const analysis = await invariantAnalyzer.analyzeInvariant(invariant, context);
      
      // Output results
      if (options.verbose) {
        console.log("\nInvariant Analysis:");
        console.log(`  Invariant: ${analysis.invariant}`);
        console.log(`  Category: ${analysis.category}`);
        console.log(`  Complexity: ${analysis.complexity}`);
        console.log(`  Estimated Steps: ${analysis.estimatedSteps}`);
        console.log(`  Dependencies: ${analysis.dependencies.join(", ")}`);
        
        console.log("\nProof Strategy:");
        console.log(`  Type: ${analysis.proofStrategy.type}`);
        console.log(`  Approach: ${analysis.proofStrategy.approach}`);
        console.log(`  Required Lemmas: ${analysis.proofStrategy.requiredLemmas.join(", ")}`);
        console.log(`  Proof Steps: ${analysis.proofStrategy.proofSteps.length}`);
        
        console.log("\nProof Steps:");
        analysis.proofStrategy.proofSteps.forEach((step, index) => {
          console.log(`  ${index + 1}. ${step.stepType}: ${step.description}`);
          console.log(`     Budget: ${step.budget}`);
          console.log(`     Dependencies: ${step.dependencies.join(", ")}`);
        });
      } else {
        console.log(`✓ Analysis completed`);
        console.log(`  Category: ${analysis.category}`);
        console.log(`  Complexity: ${analysis.complexity}`);
        console.log(`  Strategy: ${analysis.proofStrategy.type} - ${analysis.proofStrategy.approach}`);
        console.log(`  Steps: ${analysis.estimatedSteps}`);
      }
      
    } catch (error) {
      console.error(`Error analyzing invariant: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// Compose multiple proofs
program
  .command("compose")
  .description("Compose multiple proofs into a proof chain")
  .argument("<name>", "Name for the proof chain")
  .argument("<proofs...>", "Paths to proof files to compose")
  .option("-s, --strategy <type>", "Composition strategy", "sequential")
  .option("-o, --output <path>", "Output directory for composed proof")
  .option("-v, --verbose", "Verbose output")
  .action(async (name: string, proofs: string[], options: any) => {
    try {
      console.log(`Composing proof chain: ${name}`);
      console.log(`  Proofs: ${proofs.length}`);
      console.log(`  Strategy: ${options.strategy}`);
      
      // Load proofs
      const loadedProofs = [];
      for (const proofPath of proofs) {
        if (!fs.existsSync(proofPath)) {
          console.error(`Proof file not found: ${proofPath}`);
          process.exit(1);
        }
        const proof = JSON.parse(fs.readFileSync(proofPath, "utf8"));
        loadedProofs.push(proof);
      }
      
      // Create composition strategy
      const strategy = {
        type: options.strategy as "sequential" | "parallel" | "hierarchical" | "conditional",
        approach: `${options.strategy}_composition`,
        compositionRules: [],
        optimizationLevel: "basic" as const
      };
      
      // Compose proofs
      const proofChain = await proofComposer.composeProofChain(name, loadedProofs, strategy);
      
      // Output results
      if (options.verbose) {
        console.log("\nProof Chain Details:");
        console.log(`  ID: ${proofChain.id}`);
        console.log(`  Name: ${proofChain.name}`);
        console.log(`  Proofs: ${proofChain.proofs.length}`);
        console.log(`  Verification Result: ${proofChain.verificationResult ? "PASS" : "FAIL"}`);
        console.log(`  Confidence: ${proofChain.confidence.toFixed(3)}`);
        console.log(`  Complexity: ${proofChain.metadata.complexity}`);
        console.log(`  Total Steps: ${proofChain.metadata.totalSteps}`);
        console.log(`  Total Budget: ${proofChain.metadata.totalBudget}`);
        console.log(`  Dependencies: ${proofChain.dependencies.join(", ")}`);
      } else {
        console.log(`✓ Proof chain composed successfully`);
        console.log(`  ID: ${proofChain.id}`);
        console.log(`  Verification: ${proofChain.verificationResult ? "PASS" : "FAIL"}`);
        console.log(`  Confidence: ${proofChain.confidence.toFixed(3)}`);
        console.log(`  Steps: ${proofChain.metadata.totalSteps}`);
      }
      
      // Save to output directory if specified
      if (options.output) {
        const outputDir = path.resolve(options.output);
        if (!fs.existsSync(outputDir)) {
          fs.mkdirSync(outputDir, { recursive: true });
        }
        
        const outputFile = path.join(outputDir, `${name}_chain.json`);
        fs.writeFileSync(outputFile, JSON.stringify(proofChain, null, 2));
        console.log(`  Saved to: ${outputFile}`);
      }
      
    } catch (error) {
      console.error(`Error composing proofs: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// Batch generate proofs for multiple invariants
program
  .command("batch-generate")
  .description("Generate proofs for multiple invariants")
  .argument("<invariants...>", "Invariants to generate proofs for")
  .option("-m, --module <path>", "Path to module file")
  .option("-o, --output <path>", "Output directory for generated proofs")
  .option("-v, --verbose", "Verbose output")
  .action(async (invariants: string[], options: any) => {
    try {
      console.log(`Batch generating proofs for ${invariants.length} invariants`);
      
      // Load module data if provided
      let moduleData = {};
      if (options.module) {
        if (!fs.existsSync(options.module)) {
          console.error(`Module file not found: ${options.module}`);
          process.exit(1);
        }
        moduleData = JSON.parse(fs.readFileSync(options.module, "utf8"));
      }
      
      // Create verification context
      const context: VerificationContext = {
        moduleData,
        referenceFingerprint: undefined,
        performanceMetrics: metrics,
        executionEnvironment: {
          nodeVersion: process.version,
          platform: process.platform,
          arch: process.arch
        }
      };
      
      // Generate proofs
      const results = [];
      for (const invariant of invariants) {
        try {
          console.log(`  Generating proof for: ${invariant}`);
          const generatedProof = await proofGenerator.generateProofForInvariant(invariant, context);
          results.push(generatedProof);
          
          if (options.verbose) {
            console.log(`    ✓ Generated (confidence: ${generatedProof.confidence.toFixed(3)})`);
          }
        } catch (error) {
          console.error(`    ✗ Failed: ${error instanceof Error ? error.message : String(error)}`);
          results.push(null);
        }
      }
      
      // Summary
      const successful = results.filter(r => r !== null).length;
      const failed = results.length - successful;
      
      console.log(`\nBatch generation completed:`);
      console.log(`  Successful: ${successful}`);
      console.log(`  Failed: ${failed}`);
      
      // Save results if output directory specified
      if (options.output) {
        const outputDir = path.resolve(options.output);
        if (!fs.existsSync(outputDir)) {
          fs.mkdirSync(outputDir, { recursive: true });
        }
        
        for (const result of results) {
          if (result) {
            const outputFile = path.join(outputDir, `${result.invariant}_proof.json`);
            fs.writeFileSync(outputFile, JSON.stringify(result, null, 2));
          }
        }
        
        console.log(`  Results saved to: ${outputDir}`);
      }
      
    } catch (error) {
      console.error(`Error in batch generation: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// List generated proofs
program
  .command("list")
  .description("List all generated proofs")
  .option("-v, --verbose", "Verbose output")
  .action(async (options: any) => {
    try {
      const generatedProofs = proofGenerator.listGeneratedProofs();
      
      if (generatedProofs.length === 0) {
        console.log("No generated proofs found");
        return;
      }
      
      console.log(`Found ${generatedProofs.length} generated proofs:`);
      
      for (const proof of generatedProofs) {
        if (options.verbose) {
          console.log(`\n  ${proof.invariant}:`);
          console.log(`    Artifact: ${proof.proofArtifact}`);
          console.log(`    Digest: ${proof.digest}`);
          console.log(`    Verified: ${proof.verificationResult ? "PASS" : "FAIL"}`);
          console.log(`    Confidence: ${proof.confidence.toFixed(3)}`);
          console.log(`    Strategy: ${proof.metadata.strategy.type}`);
          console.log(`    Complexity: ${proof.metadata.complexity}`);
          console.log(`    Steps: ${proof.metadata.verificationSteps}`);
        } else {
          console.log(`  ${proof.invariant} (${proof.confidence.toFixed(3)}) - ${proof.verificationResult ? "PASS" : "FAIL"}`);
        }
      }
      
    } catch (error) {
      console.error(`Error listing proofs: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// Validate all proofs
program
  .command("validate-all")
  .description("Validate all generated proofs")
  .option("-v, --verbose", "Verbose output")
  .action(async (options: any) => {
    try {
      console.log("Validating all generated proofs...");
      
      const generatedProofs = proofGenerator.listGeneratedProofs();
      if (generatedProofs.length === 0) {
        console.log("No generated proofs found");
        return;
      }
      
      const validationResults = await proofVerifier.validateAllProofs(generatedProofs);
      
      console.log(`\nValidation Results:`);
      console.log(`  Total: ${validationResults.total}`);
      console.log(`  Valid: ${validationResults.valid}`);
      console.log(`  Invalid: ${validationResults.invalid}`);
      
      if (options.verbose) {
        console.log("\nDetailed Results:");
        for (const result of validationResults.results) {
          console.log(`  ${result.proof.invariant}: ${result.verified ? "PASS" : "FAIL"} (${result.confidence.toFixed(3)})`);
          if (!result.verified) {
            console.log(`    Issues: ${result.recommendations.length}`);
          }
        }
      }
      
    } catch (error) {
      console.error(`Error validating proofs: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

// Show help for specific command
program
  .command("help")
  .description("Show help for a specific command")
  .argument("[command]", "Command to show help for")
  .action((command?: string) => {
    if (command) {
      program.help();
    } else {
      program.help();
    }
  });

// Parse command line arguments
program.parse();

// If no command provided, show help
if (!process.argv.slice(2).length) {
  program.help();
}
