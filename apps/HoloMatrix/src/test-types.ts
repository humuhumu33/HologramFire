/**
 * Test type definitions
 */

declare global {
  namespace jest {
    interface Matchers<R> {
      toBeValidBudget(): R;
      toBeValidWitness(): R;
      toBeValidReceipt(): R;
      toBeValidLatticeCoord(): R;
    }
  }
  
  namespace NodeJS {
    interface ProcessEnv {
      HOLOGRAM_API_ENDPOINT?: string;
      HOLOGRAM_TIMEOUT?: string;
      HOLOGRAM_RETRIES?: string;
    }
  }
}

export {};
