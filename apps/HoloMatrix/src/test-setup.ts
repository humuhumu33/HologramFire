/**
 * Jest test setup file
 * Configures test environment and global test utilities
 */

import './test-types';

// Global test timeout
jest.setTimeout(30000);

// Suppress console methods to reduce noise in tests
const originalConsole = { ...console };
beforeAll(() => {
  console.log = jest.fn();
  console.warn = jest.fn();
  console.error = jest.fn();
});

afterAll(() => {
  console.log = originalConsole.log;
  console.warn = originalConsole.warn;
  console.error = originalConsole.error;
});

// Custom Jest matchers
expect.extend({
  toBeValidBudget(received: any) {
    const pass = received &&
      typeof received.cpuMs === 'number' &&
      typeof received.io === 'number' &&
      typeof received.mem === 'number' &&
      received.cpuMs >= 0 &&
      received.io >= 0 &&
      received.mem >= 0;

    return {
      message: () => `expected ${received} to be a valid budget`,
      pass
    };
  },

  toBeValidWitness(received: any) {
    const pass = received &&
      typeof received.r96 === 'string' &&
      typeof received.timestamp === 'number' &&
      typeof received.nodeId === 'string' &&
      received.r96.length > 0 &&
      received.timestamp > 0 &&
      received.nodeId.length > 0;

    return {
      message: () => `expected ${received} to be a valid witness`,
      pass
    };
  },

  toBeValidReceipt(received: any) {
    const pass = received &&
      typeof received.id === 'string' &&
      typeof received.closed === 'boolean' &&
      typeof received.timestamp === 'number' &&
      typeof received.gate === 'string' &&
      received.id.length > 0 &&
      received.timestamp > 0 &&
      received.gate.length > 0;

    return {
      message: () => `expected ${received} to be a valid receipt`,
      pass
    };
  },

  toBeValidLatticeCoord(received: any) {
    const pass = received &&
      typeof received.r === 'number' &&
      typeof received.c === 'number' &&
      received.r >= 0 && received.r < 48 &&
      received.c >= 0 && received.c < 256;

    return {
      message: () => `expected ${received} to be a valid lattice coordinate`,
      pass
    };
  }
});

// Test environment setup
beforeEach(() => {
  // Reset environment variables
  delete process.env['HOLOGRAM_USE_MOCK'];
  delete process.env['MOCK_SPEED_FACTOR'];
});

afterEach(() => {
  // Clean up after each test
  jest.clearAllMocks();
});
