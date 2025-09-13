/**
 * Hologram SDK Adapter
 * 
 * This adapter switches between the mock implementation and the real Hologram SDK
 * based on the HOLOGRAM_USE_MOCK environment variable.
 * 
 * To use the real SDK:
 * 1. Set HOLOGRAM_USE_MOCK=false
 * 2. The real SDK implementation will be used automatically
 */

import * as mockSDK from './mock';
import * as realSDK from './real-sdk';

// Check if we should use the mock implementation
const useMock = process.env['HOLOGRAM_USE_MOCK'] !== 'false';

if (useMock) {
  console.log('🔧 Using MOCK Hologram SDK implementation');
} else {
  console.log('🚀 Using REAL Hologram SDK implementation');
}

// Export the appropriate implementation
export const createVerifier = useMock ? mockSDK.createVerifier : realSDK.createVerifier;
export const createCTP = useMock ? mockSDK.createCTP : realSDK.createCTP;
export const createStorage = useMock ? mockSDK.createStorage : realSDK.createStorage;
export const spawnKernel = useMock ? mockSDK.spawnKernel : realSDK.spawnKernel;
export const uorIdFromBytes = useMock ? mockSDK.uorIdFromBytes : realSDK.uorIdFromBytes;
export const place = useMock ? mockSDK.place : realSDK.place;

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
