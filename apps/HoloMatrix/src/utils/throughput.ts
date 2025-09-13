/**
 * Accurate Throughput Measurement Utilities
 * Provides consistent and accurate throughput calculations across HoloMatrix
 */

export interface ThroughputMeasurement {
  dataProcessedBytes: number;
  computationTimeSeconds: number;
  throughputGbps: number;
  isValid: boolean;
}

export interface MatrixDataInfo {
  matrixSize: number;
  blockSize: number;
  totalBlocks: number;
  bytesPerBlock: number;
  totalDataBytes: number;
}

/**
 * Calculate matrix data information for accurate throughput measurement
 * For matrix multiplication, we need to account for the actual data movement during computation
 */
export function calculateMatrixDataInfo(matrixSize: number, blockSize: number): MatrixDataInfo {
  const blockCount = Math.ceil(matrixSize / blockSize);
  
  // For matrix multiplication A * B = C, we need to account for the actual data movement:
  // Each block multiplication involves reading A blocks, B blocks, and writing C blocks
  // The total data movement is much higher than just the matrix sizes
  
  const blocksPerMatrix = blockCount * blockCount;
  const bytesPerBlock = blockSize * blockSize * 2; // Int16 values (2 bytes each)
  
  // For each output block C[i,j], we need to:
  // 1. Read all A[i,k] blocks (blockCount reads)
  // 2. Read all B[k,j] blocks (blockCount reads) 
  // 3. Write the result C[i,j] (1 write)
  // Total data movement per output block = blockCount * bytesPerBlock * 2 + bytesPerBlock
  // Total data movement = blocksPerMatrix * (blockCount * bytesPerBlock * 2 + bytesPerBlock)
  
  const dataMovementPerOutputBlock = blockCount * bytesPerBlock * 2 + bytesPerBlock;
  const totalDataBytes = blocksPerMatrix * dataMovementPerOutputBlock;
  const totalBlocks = blocksPerMatrix * 3; // A, B, and C matrices

  return {
    matrixSize,
    blockSize,
    totalBlocks,
    bytesPerBlock,
    totalDataBytes
  };
}

/**
 * Calculate accurate throughput measurement
 */
export function calculateThroughput(
  dataProcessedBytes: number,
  computationTimeSeconds: number
): ThroughputMeasurement {
  const isValid = dataProcessedBytes > 0 && computationTimeSeconds > 0;
  const throughputGbps = isValid ? (dataProcessedBytes * 8) / (computationTimeSeconds * 1e9) : 0;

  return {
    dataProcessedBytes,
    computationTimeSeconds,
    throughputGbps,
    isValid
  };
}

/**
 * Validate throughput measurement against requirements
 */
export function validateThroughput(
  measurement: ThroughputMeasurement,
  requiredGbps: number
): { passed: boolean; actual: number; required: number; message: string } {
  const passed = measurement.isValid && measurement.throughputGbps >= requiredGbps;
  const message = passed 
    ? `✅ Throughput: ${measurement.throughputGbps.toFixed(2)} Gbit/s ≥ ${requiredGbps} Gbit/s`
    : `❌ Throughput: ${measurement.throughputGbps.toFixed(2)} Gbit/s < ${requiredGbps} Gbit/s required`;

  return {
    passed,
    actual: measurement.throughputGbps,
    required: requiredGbps,
    message
  };
}

/**
 * Format throughput measurement for display
 */
export function formatThroughput(measurement: ThroughputMeasurement): string {
  if (!measurement.isValid) {
    return "Invalid measurement";
  }

  const dataGB = measurement.dataProcessedBytes / (1024 * 1024 * 1024);
  const timeFormatted = measurement.computationTimeSeconds.toFixed(2);
  const throughputFormatted = measurement.throughputGbps.toFixed(2);

  return `${dataGB.toFixed(2)} GB in ${timeFormatted}s = ${throughputFormatted} Gbit/s`;
}

/**
 * Create a throughput timer for accurate measurement
 */
export class ThroughputTimer {
  private startTime: number = 0;
  private endTime: number = 0;
  private isRunning: boolean = false;

  start(): void {
    this.startTime = Date.now();
    this.isRunning = true;
  }

  stop(): void {
    if (this.isRunning) {
      this.endTime = Date.now();
      this.isRunning = false;
    }
  }

  getElapsedSeconds(): number {
    const endTime = this.isRunning ? Date.now() : this.endTime;
    return (endTime - this.startTime) / 1000;
  }

  isActive(): boolean {
    return this.isRunning;
  }

  reset(): void {
    this.startTime = 0;
    this.endTime = 0;
    this.isRunning = false;
  }
}
