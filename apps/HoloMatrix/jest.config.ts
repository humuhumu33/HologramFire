import type { Config } from "jest";

const config: Config = {
  preset: "ts-jest",
  testEnvironment: "node",
  testMatch: ["**/*.test.ts"],
  globals: { "ts-jest": { tsconfig: "tsconfig.json" } },
  testTimeout: 30000,
  setupFilesAfterEnv: ["<rootDir>/src/test-setup.ts"],
};
export default config;
