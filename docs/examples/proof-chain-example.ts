import { ProofChainAPI, createProofChainAPI } from '../src/proof-chain/ProofChainAPI';
import { ProofNode, ProofChain } from '../src/proof-chain/ProofChain';

/**
 * Comprehensive Example: Data Transformation Proof Chain
 * 
 * This example demonstrates a complete chain of proofs for a simple data transformation
 * pipeline, showing full provenance tracking from raw data to final result.
 * 
 * Pipeline Steps:
 * 1. Data Validation - Validate input data structure
 * 2. Data Cleaning - Remove invalid entries and normalize
 * 3. Data Enrichment - Add computed fields and aggregations
 * 4. Data Transformation - Apply business logic transformations
 * 5. Data Serialization - Convert to final output format
 * 6. Data Verification - Verify final result integrity
 */

interface RawDataEntry {
  id: string;
  name: string;
  email: string;
  age: number;
  salary: number;
  department: string;
  joinDate: string;
}

interface CleanedDataEntry extends RawDataEntry {
  isValid: boolean;
  normalizedEmail: string;
  ageGroup: string;
}

interface EnrichedDataEntry extends CleanedDataEntry {
  yearsOfService: number;
  salaryGrade: string;
  performanceScore: number;
}

interface TransformedDataEntry extends EnrichedDataEntry {
  displayName: string;
  compensation: {
    base: number;
    bonus: number;
    total: number;
  };
  status: string;
}

interface FinalResult {
  summary: {
    totalEmployees: number;
    averageSalary: number;
    departmentBreakdown: Record<string, number>;
    ageDistribution: Record<string, number>;
  };
  employees: TransformedDataEntry[];
  metadata: {
    processingTime: number;
    dataQuality: number;
    transformations: string[];
  };
}

class DataTransformationProofExample {
  private api: ProofChainAPI;
  private chainResults: any[] = [];

  constructor() {
    // Initialize the proof chain API with monitoring enabled
    this.api = createProofChainAPI({
      enableMonitoring: true,
      enableCompliance: true,
      enableProvenance: true,
      autoStartMonitoring: true
    });
  }

  /**
   * Main execution method that runs the complete data transformation pipeline
   */
  async runCompletePipeline(): Promise<{
    finalResult: FinalResult;
    proofChain: {
      chainId: string;
      totalNodes: number;
      verificationStatus: string;
      provenance: any[];
    };
    verification: any;
  }> {
    console.log('🚀 Starting Data Transformation Proof Chain Example');
    console.log('=' .repeat(60));

    // Sample raw data
    const rawData: RawDataEntry[] = [
      {
        id: 'EMP001',
        name: 'John Doe',
        email: 'john.doe@company.com',
        age: 32,
        salary: 75000,
        department: 'Engineering',
        joinDate: '2020-03-15'
      },
      {
        id: 'EMP002',
        name: 'Jane Smith',
        email: 'jane.smith@company.com',
        age: 28,
        salary: 68000,
        department: 'Marketing',
        joinDate: '2021-07-22'
      },
      {
        id: 'EMP003',
        name: 'Bob Johnson',
        email: 'bob.johnson@company.com',
        age: 45,
        salary: 95000,
        department: 'Engineering',
        joinDate: '2018-11-08'
      },
      {
        id: 'EMP004',
        name: 'Alice Brown',
        email: 'alice.brown@company.com',
        age: 35,
        salary: 82000,
        department: 'Sales',
        joinDate: '2019-05-12'
      },
      {
        id: 'EMP005',
        name: 'Charlie Wilson',
        email: 'invalid-email',
        age: -5, // Invalid age
        salary: 0, // Invalid salary
        department: '',
        joinDate: 'invalid-date'
      }
    ];

    console.log(`📊 Processing ${rawData.length} employee records`);
    console.log('');

    // Step 1: Data Validation
    console.log('🔍 Step 1: Data Validation');
    const validationResult = await this.api.transformData(
      'validate_employee_data',
      rawData,
      this.validateEmployeeData,
      {
        transformationType: 'validate',
        invariants: [
          'All employees must have valid IDs',
          'Email addresses must be properly formatted',
          'Age must be positive integer',
          'Salary must be positive number',
          'Department must not be empty',
          'Join date must be valid ISO date'
        ]
      }
    );
    this.chainResults.push(validationResult);
    console.log(`   ✅ Validation completed - Proof: ${validationResult.proofNodeId}`);
    console.log(`   📈 Confidence: ${(validationResult.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Step 2: Data Cleaning
    console.log('🧹 Step 2: Data Cleaning');
    const cleaningResult = await this.api.transformData(
      'clean_employee_data',
      validationResult.result,
      this.cleanEmployeeData,
      {
        transformationType: 'filter',
        invariants: [
          'Remove invalid entries',
          'Normalize email addresses',
          'Categorize age groups',
          'Maintain data integrity'
        ],
        parentProofs: [validationResult.proofNodeId]
      }
    );
    this.chainResults.push(cleaningResult);
    console.log(`   ✅ Cleaning completed - Proof: ${cleaningResult.proofNodeId}`);
    console.log(`   📈 Confidence: ${(cleaningResult.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Step 3: Data Enrichment
    console.log('✨ Step 3: Data Enrichment');
    const enrichmentResult = await this.api.transformData(
      'enrich_employee_data',
      cleaningResult.result,
      this.enrichEmployeeData,
      {
        transformationType: 'map',
        invariants: [
          'Calculate years of service',
          'Determine salary grade',
          'Compute performance score',
          'Preserve original data integrity'
        ],
        parentProofs: [cleaningResult.proofNodeId]
      }
    );
    this.chainResults.push(enrichmentResult);
    console.log(`   ✅ Enrichment completed - Proof: ${enrichmentResult.proofNodeId}`);
    console.log(`   📈 Confidence: ${(enrichmentResult.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Step 4: Data Transformation
    console.log('🔄 Step 4: Data Transformation');
    const transformationResult = await this.api.transformData(
      'transform_employee_data',
      enrichmentResult.result,
      this.transformEmployeeData,
      {
        transformationType: 'map',
        invariants: [
          'Generate display names',
          'Calculate compensation packages',
          'Determine employment status',
          'Maintain holographic correspondence'
        ],
        parentProofs: [enrichmentResult.proofNodeId]
      }
    );
    this.chainResults.push(transformationResult);
    console.log(`   ✅ Transformation completed - Proof: ${transformationResult.proofNodeId}`);
    console.log(`   📈 Confidence: ${(transformationResult.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Step 5: Data Aggregation
    console.log('📊 Step 5: Data Aggregation');
    const aggregationResult = await this.api.transformData(
      'aggregate_employee_data',
      transformationResult.result,
      this.aggregateEmployeeData,
      {
        transformationType: 'reduce',
        invariants: [
          'Calculate summary statistics',
          'Generate department breakdown',
          'Compute age distribution',
          'Preserve individual record integrity'
        ],
        parentProofs: [transformationResult.proofNodeId]
      }
    );
    this.chainResults.push(aggregationResult);
    console.log(`   ✅ Aggregation completed - Proof: ${aggregationResult.proofNodeId}`);
    console.log(`   📈 Confidence: ${(aggregationResult.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Step 6: Final Verification
    console.log('🔐 Step 6: Final Verification');
    const verificationResult = await this.api.compute(
      'verify_final_result',
      aggregationResult.result,
      this.verifyFinalResult,
      {
        computationType: 'verification',
        algorithm: 'integrity_check',
        invariants: [
          'Verify data consistency',
          'Check calculation accuracy',
          'Validate business rules',
          'Confirm holographic correspondence'
        ],
        parentProofs: [aggregationResult.proofNodeId]
      }
    );
    this.chainResults.push(verificationResult);
    console.log(`   ✅ Verification completed - Proof: ${verificationResult.proofNodeId}`);
    console.log(`   📈 Confidence: ${(verificationResult.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Get the final chain ID (should be the same for all operations in the chain)
    const chainId = verificationResult.chainId;

    // Verify the entire chain
    console.log('🔗 Verifying Complete Proof Chain');
    const chainVerification = await this.api.verifyChain(chainId);
    console.log(`   Chain ID: ${chainId}`);
    console.log(`   Total Nodes: ${chainVerification.totalNodes}`);
    console.log(`   Verified Nodes: ${chainVerification.verifiedNodes}`);
    console.log(`   Failed Nodes: ${chainVerification.failedNodes}`);
    console.log(`   Overall Status: ${chainVerification.isValid ? '✅ VALID' : '❌ INVALID'}`);
    console.log(`   Chain Confidence: ${(chainVerification.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Trace provenance from start to end
    console.log('🔍 Tracing Provenance');
    const provenanceTrace = await this.api.traceProvenance(
      validationResult.proofNodeId,
      verificationResult.proofNodeId
    );
    console.log(`   Trace ID: ${provenanceTrace.traceId}`);
    console.log(`   Path Length: ${provenanceTrace.pathLength}`);
    console.log(`   Is Complete: ${provenanceTrace.isComplete ? '✅' : '❌'}`);
    console.log(`   Trace Confidence: ${(provenanceTrace.confidence * 100).toFixed(1)}%`);
    console.log('');

    // Generate compliance report
    console.log('📋 Generating Compliance Report');
    const complianceReport = await this.api.generateComplianceReport();
    console.log(`   Total Operations: ${complianceReport.totalOperations}`);
    console.log(`   Compliance Score: ${(complianceReport.complianceScore * 100).toFixed(1)}%`);
    console.log(`   Violations: ${complianceReport.violations.length}`);
    console.log(`   Warnings: ${complianceReport.warnings.length}`);
    console.log('');

    // Get system statistics
    const stats = this.api.getChainStatistics();
    console.log('📈 System Statistics');
    console.log(`   Total Chains: ${stats.totalChains}`);
    console.log(`   Total Nodes: ${stats.totalNodes}`);
    console.log(`   Verified Chains: ${stats.verifiedChains}`);
    console.log(`   Average Chain Length: ${stats.averageChainLength.toFixed(1)}`);
    console.log('');

    return {
      finalResult: verificationResult.result,
      proofChain: {
        chainId,
        totalNodes: chainVerification.totalNodes,
        verificationStatus: chainVerification.isValid ? 'verified' : 'failed',
        provenance: this.chainResults.map(r => ({
          operation: r.result.operation || 'unknown',
          proofNodeId: r.proofNodeId,
          confidence: r.confidence,
          executionTime: r.executionTimeMs
        }))
      },
      verification: {
        chainVerification,
        provenanceTrace,
        complianceReport
      }
    };
  }

  /**
   * Step 1: Data Validation
   */
  private validateEmployeeData = (data: RawDataEntry[]): RawDataEntry[] => {
    console.log('   🔍 Validating employee data structure and content...');
    
    const validatedData = data.filter(entry => {
      const isValid = !!(
        entry.id &&
        entry.name &&
        entry.email &&
        entry.age > 0 &&
        entry.salary > 0 &&
        entry.department &&
        entry.joinDate &&
        this.isValidEmail(entry.email) &&
        this.isValidDate(entry.joinDate)
      );
      
      if (!isValid) {
        console.log(`   ⚠️  Invalid entry filtered out: ${entry.id}`);
      }
      
      return isValid;
    });

    console.log(`   📊 Validated ${validatedData.length} out of ${data.length} entries`);
    return validatedData;
  };

  /**
   * Step 2: Data Cleaning
   */
  private cleanEmployeeData = (data: RawDataEntry[]): CleanedDataEntry[] => {
    console.log('   🧹 Cleaning and normalizing employee data...');
    
    const cleanedData: CleanedDataEntry[] = data.map(entry => ({
      ...entry,
      isValid: true,
      normalizedEmail: entry.email.toLowerCase().trim(),
      ageGroup: this.categorizeAge(entry.age)
    }));

    console.log(`   📊 Cleaned ${cleanedData.length} employee records`);
    return cleanedData;
  };

  /**
   * Step 3: Data Enrichment
   */
  private enrichEmployeeData = (data: CleanedDataEntry[]): EnrichedDataEntry[] => {
    console.log('   ✨ Enriching employee data with computed fields...');
    
    const enrichedData: EnrichedDataEntry[] = data.map(entry => {
      const yearsOfService = this.calculateYearsOfService(entry.joinDate);
      const salaryGrade = this.determineSalaryGrade(entry.salary);
      const performanceScore = this.calculatePerformanceScore(entry);

      return {
        ...entry,
        yearsOfService,
        salaryGrade,
        performanceScore
      };
    });

    console.log(`   📊 Enriched ${enrichedData.length} employee records`);
    return enrichedData;
  };

  /**
   * Step 4: Data Transformation
   */
  private transformEmployeeData = (data: EnrichedDataEntry[]): TransformedDataEntry[] => {
    console.log('   🔄 Transforming employee data with business logic...');
    
    const transformedData: TransformedDataEntry[] = data.map(entry => {
      const displayName = `${entry.name} (${entry.department})`;
      const bonus = this.calculateBonus(entry);
      const totalCompensation = entry.salary + bonus;
      const status = this.determineEmploymentStatus(entry);

      return {
        ...entry,
        displayName,
        compensation: {
          base: entry.salary,
          bonus,
          total: totalCompensation
        },
        status
      };
    });

    console.log(`   📊 Transformed ${transformedData.length} employee records`);
    return transformedData;
  };

  /**
   * Step 5: Data Aggregation
   */
  private aggregateEmployeeData = (data: TransformedDataEntry[]): FinalResult => {
    console.log('   📊 Aggregating employee data into summary statistics...');
    
    const totalEmployees = data.length;
    const averageSalary = data.reduce((sum, emp) => sum + emp.salary, 0) / totalEmployees;
    
    const departmentBreakdown = data.reduce((acc, emp) => {
      acc[emp.department] = (acc[emp.department] || 0) + 1;
      return acc;
    }, {} as Record<string, number>);
    
    const ageDistribution = data.reduce((acc, emp) => {
      acc[emp.ageGroup] = (acc[emp.ageGroup] || 0) + 1;
      return acc;
    }, {} as Record<string, number>);

    const dataQuality = this.calculateDataQuality(data);
    const processingTime = this.chainResults.reduce((sum, r) => sum + r.executionTimeMs, 0);

    const result: FinalResult = {
      summary: {
        totalEmployees,
        averageSalary,
        departmentBreakdown,
        ageDistribution
      },
      employees: data,
      metadata: {
        processingTime,
        dataQuality,
        transformations: [
          'validate_employee_data',
          'clean_employee_data',
          'enrich_employee_data',
          'transform_employee_data',
          'aggregate_employee_data'
        ]
      }
    };

    console.log(`   📊 Generated summary for ${totalEmployees} employees`);
    return result;
  };

  /**
   * Step 6: Final Verification
   */
  private verifyFinalResult = (data: FinalResult): FinalResult => {
    console.log('   🔐 Verifying final result integrity...');
    
    // Verify data consistency
    const expectedEmployeeCount = data.employees.length;
    const actualEmployeeCount = data.summary.totalEmployees;
    
    if (expectedEmployeeCount !== actualEmployeeCount) {
      throw new Error(`Employee count mismatch: expected ${expectedEmployeeCount}, got ${actualEmployeeCount}`);
    }

    // Verify salary calculation
    const expectedAvgSalary = data.employees.reduce((sum, emp) => sum + emp.salary, 0) / data.employees.length;
    const actualAvgSalary = data.summary.averageSalary;
    
    if (Math.abs(expectedAvgSalary - actualAvgSalary) > 0.01) {
      throw new Error(`Average salary mismatch: expected ${expectedAvgSalary}, got ${actualAvgSalary}`);
    }

    // Verify department breakdown
    const expectedDeptBreakdown = data.employees.reduce((acc, emp) => {
      acc[emp.department] = (acc[emp.department] || 0) + 1;
      return acc;
    }, {} as Record<string, number>);
    
    for (const [dept, count] of Object.entries(data.summary.departmentBreakdown)) {
      if (expectedDeptBreakdown[dept] !== count) {
        throw new Error(`Department breakdown mismatch for ${dept}`);
      }
    }

    console.log('   ✅ Final result verification passed');
    return data;
  };

  // Helper methods
  private isValidEmail(email: string): boolean {
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    return emailRegex.test(email);
  }

  private isValidDate(dateString: string): boolean {
    const date = new Date(dateString);
    return !isNaN(date.getTime());
  }

  private categorizeAge(age: number): string {
    if (age < 25) return 'Young';
    if (age < 35) return 'Mid';
    if (age < 50) return 'Senior';
    return 'Veteran';
  }

  private calculateYearsOfService(joinDate: string): number {
    const join = new Date(joinDate);
    const now = new Date();
    return Math.floor((now.getTime() - join.getTime()) / (365.25 * 24 * 60 * 60 * 1000));
  }

  private determineSalaryGrade(salary: number): string {
    if (salary < 50000) return 'Junior';
    if (salary < 75000) return 'Mid';
    if (salary < 100000) return 'Senior';
    return 'Executive';
  }

  private calculatePerformanceScore(entry: EnrichedDataEntry): number {
    // Simple performance score based on salary and years of service
    const baseScore = Math.min(entry.salary / 10000, 10);
    const experienceBonus = Math.min(entry.yearsOfService * 0.5, 5);
    return Math.min(baseScore + experienceBonus, 10);
  }

  private calculateBonus(entry: EnrichedDataEntry): number {
    // Bonus calculation based on performance and years of service
    const performanceBonus = entry.performanceScore * 1000;
    const loyaltyBonus = entry.yearsOfService * 500;
    return performanceBonus + loyaltyBonus;
  }

  private determineEmploymentStatus(entry: EnrichedDataEntry): string {
    if (entry.yearsOfService < 1) return 'New';
    if (entry.yearsOfService < 3) return 'Established';
    if (entry.yearsOfService < 10) return 'Experienced';
    return 'Veteran';
  }

  private calculateDataQuality(data: TransformedDataEntry[]): number {
    // Simple data quality score based on completeness and consistency
    let qualityScore = 1.0;
    
    for (const entry of data) {
      if (!entry.displayName) qualityScore -= 0.1;
      if (!entry.compensation) qualityScore -= 0.1;
      if (!entry.status) qualityScore -= 0.1;
      if (entry.compensation.total <= 0) qualityScore -= 0.05;
    }
    
    return Math.max(0, qualityScore);
  }

  /**
   * Display the complete proof chain in a readable format
   */
  displayProofChain(): void {
    console.log('🔗 Complete Proof Chain Visualization');
    console.log('=' .repeat(60));
    
    this.chainResults.forEach((result, index) => {
      console.log(`Step ${index + 1}: ${result.result.operation || 'Unknown Operation'}`);
      console.log(`  Proof Node ID: ${result.proofNodeId}`);
      console.log(`  Chain ID: ${result.chainId}`);
      console.log(`  Verification: ${result.verificationStatus}`);
      console.log(`  Confidence: ${(result.confidence * 100).toFixed(1)}%`);
      console.log(`  Execution Time: ${result.executionTimeMs}ms`);
      console.log('');
    });
  }

  /**
   * Shutdown the API
   */
  shutdown(): void {
    this.api.shutdown();
  }
}

// Export the example class and a convenience function
export { DataTransformationProofExample };

export const runProofChainExample = async (): Promise<void> => {
  const example = new DataTransformationProofExample();
  
  try {
    const result = await example.runCompletePipeline();
    
    console.log('🎉 Data Transformation Proof Chain Example Completed Successfully!');
    console.log('=' .repeat(60));
    console.log('');
    
    // Display final results
    console.log('📊 Final Results Summary:');
    console.log(`   Total Employees: ${result.finalResult.summary.totalEmployees}`);
    console.log(`   Average Salary: $${result.finalResult.summary.averageSalary.toFixed(2)}`);
    console.log(`   Departments: ${Object.keys(result.finalResult.summary.departmentBreakdown).join(', ')}`);
    console.log(`   Data Quality Score: ${(result.finalResult.metadata.dataQuality * 100).toFixed(1)}%`);
    console.log('');
    
    // Display proof chain
    example.displayProofChain();
    
    // Display verification results
    console.log('🔍 Verification Results:');
    console.log(`   Chain Valid: ${result.verification.chainVerification.isValid ? '✅' : '❌'}`);
    console.log(`   Chain Confidence: ${(result.verification.chainVerification.confidence * 100).toFixed(1)}%`);
    console.log(`   Provenance Complete: ${result.verification.provenanceTrace.isComplete ? '✅' : '❌'}`);
    console.log(`   Compliance Score: ${(result.verification.complianceReport.complianceScore * 100).toFixed(1)}%`);
    console.log('');
    
  } catch (error) {
    console.error('❌ Example failed:', error);
  } finally {
    example.shutdown();
  }
};

// Run the example if this file is executed directly
if (require.main === module) {
  runProofChainExample().catch(console.error);
}
