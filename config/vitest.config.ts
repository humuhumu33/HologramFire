import { defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
    // Avoid race conditions between tests that touch filesystem
    sequence: { concurrent: false },
    hookTimeout: 30000,
    testTimeout: 30000,
    include: [
      'tests/**/*.spec.ts',
      'tests/**/*.test.ts',
    ],
    exclude: [
      '**/node_modules/**',
      '**/dist/**',
      '**/build/**',
      '**/examples/**',
      '**/chess-app/**',
      'examples/**',
      '**/examples/chess-app/**',
    ],
    // Force vitest to only look in the tests directory
    testMatch: ['<rootDir>/tests/**/*.{test,spec}.{js,ts}'],
  },
});
