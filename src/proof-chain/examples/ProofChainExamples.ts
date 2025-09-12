/**
 * Proof Chain Examples
 * 
 * Demonstrates how to use the proof chain system for various operations.
 * Shows integration with existing hologram operations and best practices.
 */

import { 
  ProofChainAPI, 
  createProofChainAPI, 
  withProof,
  verifyChain,
  traceProvenance,
  OperationResult
} from "../ProofChainAPI";

/**
 * Example 1: Basic Data Transformation with Proof
 */
export async function basicDataTransformationExample() {
  // Create proof chain API
  const api = createProofChainAPI({
    enableMonitoring: true,
    enableCompliance: true,
    enableProvenance: true
  });

  // Define a simple data transformation
  const transformData = (input: number[]): number[] => {
    return input.map(x => x * 2).filter(x => x > 10);
  };

  // Execute transformation with proof
  const result = await api.transformData(
    "double_and_filter",
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    transformData,
    {
      transformationType: "map",
      invariants: ["output_length_less_than_input", "all_outputs_greater_than_10"]
    }
  );

  console.log("Transformation Result:", result);
  console.log("Proof Node ID:", result.proofNodeId);
  console.log("Chain ID:", result.chainId);
  console.log("Verification Status:", result.verificationStatus);
  console.log("Confidence:", result.confidence);

  return result;
}

/**
 * Example 2: Computation with Proof
 */
export async function computationWithProofExample() {
  const api = createProofChainAPI();

  // Define a mathematical computation
  const computeFibonacci = (n: number): number => {
    if (n <= 1) return n;
    let a = 0, b = 1;
    for (let i = 2; i <= n; i++) {
      const temp = a + b;
      a = b;
      b = temp;
    }
    return b;
  };

  // Execute computation with proof
  const result = await api.compute(
    "fibonacci_calculation",
    10,
    computeFibonacci,
    {
      computationType: "calculation",
      algorithm: "iterative_fibonacci",
      parameters: {
        precision: 1e-6,
        maxSteps: 1000
      },
      invariants: ["fibonacci_property", "positive_result"]
    }
  );

  console.log("Computation Result:", result);
  return result;
}

/**
 * Example 3: Chaining Operations
 */
export async function chainingOperationsExample() {
  const api = createProofChainAPI();

  // Define multiple operations
  const operations = [
    {
      type: "transform" as const,
      operation: "normalize_data",
      transformFn: (input: number[]) => {
        const sum = input.reduce((a, b) => a + b, 0);
        return input.map(x => x / sum);
      },
      options: {
        transformationType: "normalize" as const,
        invariants: ["sum_equals_one"]
      }
    },
    {
      type: "compute" as const,
      operation: "calculate_entropy",
      computeFn: (input: number[]) => {
        return -input.reduce((sum, p) => sum + (p * Math.log2(p)), 0);
      },
      options: {
        computationType: "calculation" as const,
        algorithm: "shannon_entropy",
        invariants: ["entropy_non_negative"]
      }
    },
    {
      type: "transform" as const,
      operation: "round_entropy",
      transformFn: (input: number) => Math.round(input * 100) / 100,
      options: {
        transformationType: "map" as const,
        invariants: ["rounded_to_two_decimals"]
      }
    }
  ];

  // Execute chained operations
  const results = await api.chainOperations(operations, [0.1, 0.2, 0.3, 0.4]);

  console.log("Chained Operations Results:");
  results.forEach((result, index) => {
    console.log(`Step ${index + 1}:`, result.result);
    console.log(`  Proof Node ID: ${result.proofNodeId}`);
    console.log(`  Verification Status: ${result.verificationStatus}`);
  });

  return results;
}

/**
 * Example 4: Using the withProof convenience function
 */
export async function withProofExample() {
  const api = createProofChainAPI();

  // Define a complex operation
  const complexOperation = (input: { data: number[], weights: number[] }) => {
    const weightedSum = input.data.reduce((sum, value, index) => 
      sum + (value * input.weights[index]), 0
    );
    const weightedAverage = weightedSum / input.weights.reduce((sum, w) => sum + w, 0);
    return { weightedSum, weightedAverage };
  };

  // Execute with proof using convenience function
  const result = await withProof(
    api,
    "weighted_average_calculation",
    { data: [1, 2, 3, 4, 5], weights: [0.1, 0.2, 0.3, 0.2, 0.2] },
    complexOperation,
    {
      type: "compute",
      invariants: ["weighted_average_bounded", "weights_sum_to_one"]
    }
  );

  console.log("With Proof Result:", result);
  return result;
}

/**
 * Example 5: Verification and Provenance Tracing
 */
export async function verificationAndProvenanceExample() {
  const api = createProofChainAPI();

  // Execute some operations to create a chain
  const step1 = await api.transformData(
    "step1_normalize",
    [1, 2, 3, 4, 5],
    (input) => input.map(x => x / 15),
    { invariants: ["normalized_sum"] }
  );

  const step2 = await api.compute(
    "step2_entropy",
    step1.result,
    (input) => -input.reduce((sum, p) => sum + (p * Math.log2(p)), 0),
    { 
      parentProofs: [step1.proofNodeId],
      invariants: ["entropy_calculation"] 
    }
  );

  const step3 = await api.transformData(
    "step3_round",
    step2.result,
    (input) => Math.round(input * 100) / 100,
    { 
      parentProofs: [step2.proofNodeId],
      invariants: ["rounded_result"] 
    }
  );

  // Verify the entire chain
  const chainVerification = await verifyChain(api, step1.chainId);
  console.log("Chain Verification:", chainVerification);

  // Trace provenance from start to end
  const provenanceTrace = await traceProvenance(api, step1.proofNodeId, step3.proofNodeId);
  console.log("Provenance Trace:", provenanceTrace);

  return {
    operations: [step1, step2, step3],
    chainVerification,
    provenanceTrace
  };
}

/**
 * Example 6: Monitoring and Compliance
 */
export async function monitoringAndComplianceExample() {
  const api = createProofChainAPI({
    enableMonitoring: true,
    enableCompliance: true,
    enableProvenance: true,
    autoStartMonitoring: true
  });

  // Execute some operations
  await api.transformData("op1", [1, 2, 3], (x) => x.map(n => n * 2));
  await api.compute("op2", 42, (x) => x * x);
  await api.transformData("op3", "hello", (x) => x.toUpperCase());

  // Wait a bit for monitoring to collect data
  await new Promise(resolve => setTimeout(resolve, 2000));

  // Get compliance report
  const complianceReport = await api.generateComplianceReport();
  console.log("Compliance Report:", complianceReport);

  // Get alerts
  const alerts = api.getAlerts();
  console.log("Alerts:", alerts);

  // Get unresolved alerts
  const unresolvedAlerts = api.getUnresolvedAlerts();
  console.log("Unresolved Alerts:", unresolvedAlerts);

  // Get system metrics
  const metrics = api.getMetrics();
  console.log("System Metrics:", metrics);

  // Get chain statistics
  const statistics = api.getChainStatistics();
  console.log("Chain Statistics:", statistics);

  return {
    complianceReport,
    alerts,
    unresolvedAlerts,
    metrics,
    statistics
  };
}

/**
 * Example 7: Integration with Existing Hologram Operations
 */
export async function hologramIntegrationExample() {
  const api = createProofChainAPI();

  // Simulate existing hologram operations with proof generation
  const hologramOperations = [
    {
      name: "holographic_correspondence",
      operation: (input: any) => {
        // Simulate holographic correspondence calculation
        return { correspondence: Math.random(), fingerprint: "abc123" };
      }
    },
    {
      name: "resonance_classification",
      operation: (input: any) => {
        // Simulate resonance classification
        return { correspondence: Math.random(), fingerprint: "def456" };
      }
    },
    {
      name: "cycle_conservation",
      operation: (input: any) => {
        // Simulate cycle conservation
        return { correspondence: Math.random(), fingerprint: "ghi789" };
      }
    }
  ];

  const results: OperationResult<any>[] = [];

  for (const op of hologramOperations) {
    const result = await api.compute(
      op.name,
      { input: "test_data" },
      op.operation,
      {
        computationType: "analysis",
        algorithm: "holographic_analysis",
        invariants: ["holographic_correspondence", "resonance_classification", "cycle_conservation"]
      }
    );
    results.push(result);
  }

  console.log("Hologram Integration Results:", results);
  return results;
}

/**
 * Example 8: Error Handling and Recovery
 */
export async function errorHandlingExample() {
  const api = createProofChainAPI();

  try {
    // This operation will fail
    const result = await api.compute(
      "failing_operation",
      0,
      (input) => {
        if (input === 0) {
          throw new Error("Division by zero");
        }
        return 1 / input;
      },
      {
        invariants: ["no_division_by_zero"]
      }
    );
  } catch (error) {
    console.log("Caught expected error:", error);
  }

  // Continue with valid operations
  const validResult = await api.compute(
    "valid_operation",
    5,
    (input) => input * input,
    {
      invariants: ["positive_result"]
    }
  );

  console.log("Valid operation result:", validResult);
  return validResult;
}

/**
 * Run all examples
 */
export async function runAllExamples() {
  console.log("=== Proof Chain Examples ===");
  
  try {
    console.log("\n1. Basic Data Transformation:");
    await basicDataTransformationExample();

    console.log("\n2. Computation with Proof:");
    await computationWithProofExample();

    console.log("\n3. Chaining Operations:");
    await chainingOperationsExample();

    console.log("\n4. With Proof Convenience Function:");
    await withProofExample();

    console.log("\n5. Verification and Provenance:");
    await verificationAndProvenanceExample();

    console.log("\n6. Monitoring and Compliance:");
    await monitoringAndComplianceExample();

    console.log("\n7. Hologram Integration:");
    await hologramIntegrationExample();

    console.log("\n8. Error Handling:");
    await errorHandlingExample();

    console.log("\n=== All Examples Completed Successfully ===");
  } catch (error) {
    console.error("Example failed:", error);
  }
}
