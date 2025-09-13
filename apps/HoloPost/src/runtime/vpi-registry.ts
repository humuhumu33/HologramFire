/**
 * VPI Registry - Virtual Processing Interface Registry
 * 
 * This module implements the G7.vpi.registry.spec gate for kernel registration
 * and management. It provides the foundation for compute kernel execution
 * with proper budget management and preflight validation.
 */

import { Budget } from '../types';

export interface KernelFunction {
  (inputs: Array<{ id: string }>, budget: Budget): Promise<{
    ok: boolean;
    outputs: Array<{ id: string; witness: any }>;
    receipts?: any;
  }>;
}

export interface KernelRegistration {
  name: string;
  version: string;
  function: KernelFunction;
  defaultBudget: Budget;
  description: string;
  registeredAt: number;
}

/**
 * VPI Registry for kernel management
 */
export class VPIRegistry {
  private kernels: Map<string, KernelRegistration> = new Map();
  private isInitialized = false;

  /**
   * Initialize the VPI registry
   */
  initialize(): void {
    if (this.isInitialized) {
      return;
    }

    console.log('🔧 Initializing VPI Registry...');
    this.isInitialized = true;
    console.log('✅ VPI Registry initialized');
  }

  /**
   * Register a kernel with the VPI registry
   */
  register(
    name: string,
    version: string,
    kernelFunction: KernelFunction,
    defaultBudget: Budget,
    description: string
  ): void {
    if (!this.isInitialized) {
      throw new Error('VPI Registry not initialized');
    }

    const fullName = `${name}:${version}`;
    
    if (this.kernels.has(fullName)) {
      console.warn(`⚠️  Kernel ${fullName} already registered, updating...`);
    }

    const registration: KernelRegistration = {
      name,
      version,
      function: kernelFunction,
      defaultBudget,
      description,
      registeredAt: Date.now(),
    };

    this.kernels.set(fullName, registration);
    console.log(`✅ Registered kernel: ${fullName}`);
    console.log(`   Description: ${description}`);
    console.log(`   Default Budget: IO=${defaultBudget.io}, CPU=${defaultBudget.cpuMs}ms, MEM=${defaultBudget.mem || 0}`);
  }

  /**
   * Get a registered kernel
   */
  getKernel(name: string, version: string): KernelRegistration | undefined {
    const fullName = `${name}:${version}`;
    return this.kernels.get(fullName);
  }

  /**
   * Check if a kernel is registered
   */
  isKernelRegistered(name: string, version: string): boolean {
    const fullName = `${name}:${version}`;
    return this.kernels.has(fullName);
  }

  /**
   * List all registered kernels
   */
  listKernels(): KernelRegistration[] {
    return Array.from(this.kernels.values());
  }

  /**
   * Execute a kernel with proper budget validation
   */
  async executeKernel(
    name: string,
    version: string,
    inputs: Array<{ id: string }>,
    budget: Budget
  ): Promise<{
    ok: boolean;
    outputs: Array<{ id: string; witness: any }>;
    receipts?: any;
  }> {
    const kernel = this.getKernel(name, version);
    if (!kernel) {
      throw new Error(`Kernel ${name}:${version} not found in registry`);
    }

    // Validate budget against kernel requirements
    if (budget.io < kernel.defaultBudget.io) {
      throw new Error(`Insufficient IO budget: required ${kernel.defaultBudget.io}, provided ${budget.io}`);
    }
    if (budget.cpuMs < kernel.defaultBudget.cpuMs) {
      throw new Error(`Insufficient CPU budget: required ${kernel.defaultBudget.cpuMs}ms, provided ${budget.cpuMs}ms`);
    }
    if (budget.mem && kernel.defaultBudget.mem && budget.mem < kernel.defaultBudget.mem) {
      throw new Error(`Insufficient memory budget: required ${kernel.defaultBudget.mem}, provided ${budget.mem}`);
    }

    console.log(`🚀 Executing kernel: ${name}:${version}`);
    console.log(`   Inputs: ${inputs.length}`);
    console.log(`   Budget: IO=${budget.io}, CPU=${budget.cpuMs}ms, MEM=${budget.mem || 0}`);

    // Execute the kernel
    const result = await kernel.function(inputs, budget);
    
    console.log(`✅ Kernel execution completed: ${result.ok ? 'SUCCESS' : 'FAILED'}`);
    if (result.outputs) {
      console.log(`   Outputs: ${result.outputs.length}`);
    }

    return result;
  }

  /**
   * Get registry status
   */
  getStatus(): {
    initialized: boolean;
    kernelCount: number;
    kernels: Array<{ name: string; version: string; description: string }>;
  } {
    return {
      initialized: this.isInitialized,
      kernelCount: this.kernels.size,
      kernels: Array.from(this.kernels.values()).map(k => ({
        name: k.name,
        version: k.version,
        description: k.description,
      })),
    };
  }
}

/**
 * Global VPI Registry instance
 */
export const vpiRegistry = new VPIRegistry();

/**
 * Convenience function to register a kernel
 */
export function registerKernel(
  name: string,
  version: string,
  kernelFunction: KernelFunction,
  defaultBudget: Budget,
  description: string
): void {
  vpiRegistry.register(name, version, kernelFunction, defaultBudget, description);
}

/**
 * Convenience function to execute a kernel
 */
export async function executeKernel(
  name: string,
  version: string,
  inputs: Array<{ id: string }>,
  budget: Budget
): Promise<{
  ok: boolean;
  outputs: Array<{ id: string; witness: any }>;
  receipts?: any;
}> {
  return vpiRegistry.executeKernel(name, version, inputs, budget);
}
