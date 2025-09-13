/**
 * Hologram SDK Adapter for HoloMatrix
 * 
 * This adapter provides the real Hologram SDK implementation.
 * All operations use the actual Hologram SDK for production-ready functionality.
 */

import * as realSDK from './real-sdk';

console.log('🚀 Using REAL Hologram SDK implementation');

// Export the real SDK implementation
export const createVerifier = realSDK.createVerifier;
export const createCTP = realSDK.createCTP;
export const createStorage = realSDK.createStorage;
export const spawnKernel = realSDK.spawnKernel;
export const uorIdFromBytes = realSDK.uorIdFromBytes;
export const place = realSDK.place;
export const capabilities = realSDK.capabilities;
