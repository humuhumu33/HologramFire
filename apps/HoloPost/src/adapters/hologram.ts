/**
 * Hologram SDK Adapter
 * 
 * This adapter switches between the mock implementation and the real Hologram SDK
 * based on the HOLOGRAM_USE_MOCK environment variable.
 * 
 * To use the real SDK:
 * 1. Set HOLOGRAM_USE_MOCK=false
 * 2. Install the real Hologram SDK package
 * 3. Update the import path below to point to the actual SDK
 */

// Types are imported from mock.ts

// Check if we should use the mock implementation
const useMock = process.env['HOLOGRAM_USE_MOCK'] !== 'false';

// Always use mock implementation for now
// TODO: Replace with actual Hologram SDK imports when available
// Example:
// import { HologramSDK } from '@hologram/sdk';
// or
// import { HologramSDK } from '../../../libs/hologram-sdk';

if (!useMock) {
  console.warn('⚠️  Real Hologram SDK not yet configured.');
  console.warn('   To use the real SDK:');
  console.warn('   1. Set HOLOGRAM_USE_MOCK=false');
  console.warn('   2. Install the real Hologram SDK package');
  console.warn('   3. Update imports in src/adapters/hologram.ts');
  console.warn('   4. Map the real SDK functions to the expected interface');
  console.warn('');
  console.warn('   Falling back to mock implementation...');
}

// Export mock implementation
export {
  createVerifier,
  createCTP,
  createStorage,
  spawnKernel,
  uorIdFromBytes,
  place,
} from './mock';

/**
 * Real SDK implementation would look like this:
 * 
 * export async function createVerifier(): Promise<Verifier> {
 *   const sdk = new HologramSDK();
 *   return await sdk.createVerifier();
 * }
 * 
 * export async function createCTP(opts: CTPConfig): Promise<CTP> {
 *   const sdk = new HologramSDK();
 *   return await sdk.createCTP(opts);
 * }
 * 
 * export async function createStorage(opts: LatticeConfig): Promise<Storage> {
 *   const sdk = new HologramSDK();
 *   return await sdk.createStorage(opts);
 * }
 * 
 * export async function spawnKernel(opts: KernelConfig): Promise<Kernel> {
 *   const sdk = new HologramSDK();
 *   return await sdk.spawnKernel(opts);
 * }
 * 
 * export function uorIdFromBytes(bytes: Buffer): string {
 *   return HologramSDK.uorIdFromBytes(bytes);
 * }
 * 
 * export function place(id: string, opts: { rows: 48; cols: 256; parity?: number }): Placement[] {
 *   return HologramSDK.place(id, opts);
 * }
 */
