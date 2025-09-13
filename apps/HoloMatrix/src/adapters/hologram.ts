/**
 * Hologram Adapter Switcher
 * Switches between mock and real SDK based on HOLOGRAM_USE_MOCK environment variable
 */

import type { HologramAdapter } from '../types';

// Environment-based adapter selection
const useMock = process.env.HOLOGRAM_USE_MOCK !== 'false';

let adapter: HologramAdapter;

if (useMock) {
  // Use mock implementation for development and testing
  const { MockHologramAdapter } = require('./mock');
  adapter = new MockHologramAdapter();
} else {
  // TODO: Replace with real Hologram SDK imports
  // const { RealHologramAdapter } = require('./real');
  // adapter = new RealHologramAdapter();
  
  // For now, fall back to mock if real SDK not available
  console.warn('Real Hologram SDK not yet implemented, falling back to mock');
  const { MockHologramAdapter } = require('./mock');
  adapter = new MockHologramAdapter();
}

export default adapter;

// Re-export types for convenience
export type { HologramAdapter } from '../types';
