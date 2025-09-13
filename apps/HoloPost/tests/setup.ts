/**
 * Jest setup file
 * 
 * This file runs before all tests and sets up the test environment.
 */

// Set environment variables for testing
process.env['HOLOGRAM_USE_MOCK'] = 'false';
process.env['NODE_ENV'] = 'test';

// Increase timeout for integration tests
jest.setTimeout(30000);

// Global test utilities
global.console = {
  ...console,
  // Uncomment to suppress console.log during tests
  // log: jest.fn(),
  // debug: jest.fn(),
  // info: jest.fn(),
  // warn: jest.fn(),
  // error: jest.fn(),
};
