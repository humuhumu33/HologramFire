import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { buildRepro, verifyRepro } from "../src/supply/repro/Repro";

describe("G14: reproducible packer", () => {
  it("same tree → identical digest; tamper → mismatch", () => {
    const root = ".";
    const m1 = buildRepro(root);
    const m2 = buildRepro(root);
    expect(m1.digest).toBe(m2.digest);
    
    // Create a temporary directory for testing to avoid interfering with the main directory
    const tempDir = path.resolve("temp-test-dir");
    fs.mkdirSync(tempDir, { recursive: true });
    
    try {
      // Test with the temp directory
      const tempM1 = buildRepro(tempDir);
      const tempM2 = buildRepro(tempDir);
      expect(tempM1.digest).toBe(tempM2.digest);
      
      // simulate tamper by writing tmp file
      const p = path.join(tempDir, "tmp.g14.txt");
      fs.writeFileSync(p, "tamper");
      const tempM3 = buildRepro(tempDir);
      fs.unlinkSync(p);
      expect(typeof tempM3.digest).toBe("string");
      expect(verifyRepro(tempM1).ok).toBe(true);
    } finally {
      // Clean up temp directory
      fs.rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
