import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import cp from "node:child_process";

const j = (p:string)=> JSON.parse(fs.readFileSync(path.resolve(p),"utf8"));
const run = (cmd:string, req:any)=> {
  const p = cp.spawnSync(cmd.split(" ")[0], cmd.split(" ").slice(1), { input: JSON.stringify(req), encoding: "utf8", shell: true });
  if (p.error) throw p.error;
  return JSON.parse(p.stdout || "{}");
};

describe("G9: SDK contract and reference CLI", () => {
  it("contract has the required methods", () => {
    const c = j("sdk/contract.json");
    const names = c.methods.map((m:any)=> m.name);
    for (const n of ["ccmHash","uorId","proofVerify","ctpVerify","version"]) expect(names).toContain(n);
  });

  it("node ref CLI conforms and returns witnesses", () => {
    // Compile the CLI first to avoid ts-node configuration issues
    const compileCmd = `npx tsc sdk/ref/cli.ts --outDir temp-build --target ES2022 --module commonjs --moduleResolution node --esModuleInterop --skipLibCheck`;
    cp.execSync(compileCmd, { stdio: "ignore" });
    
    const cmd = "node temp-build/sdk/ref/cli.js";
    const ccm = run(cmd, { method:"ccmHash", params:{ object:{a:1}, domain:"sdk" } });
    expect(ccm.ok).toBeOneOf([true, undefined]); expect(typeof ccm.result.digest).toBe("string"); expect(typeof ccm.result.witness).toBe("string");

    const uor = run(cmd, { method:"uorId", params:{ object:{x:1} } });
    expect(uor.ok).toBe(true); expect(typeof uor.result.uor).toBe("string"); expect(typeof uor.result.witness).toBe("string");

    const pv = run(cmd, { method:"proofVerify", params:{ budgets:[96] } });
    expect(pv.ok).toBe(true); expect(typeof pv.result.witness).toBe("string");

    const ver = run(cmd, { method:"version" });
    expect(ver.ok).toBe(true); expect(ver.result.contract).toBe(1);
    
    // Clean up
    try {
      cp.execSync(process.platform === "win32" ? "rmdir /s /q temp-build" : "rm -rf temp-build", { stdio: "ignore" });
    } catch (e) {
      // Ignore cleanup errors
    }
  });
});
