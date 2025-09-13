import { describe, it, expect } from "vitest";
import { beginSession, recordPhase, finishSession } from "../src/ml2p/energy/Semantics";

describe("G-ML2P: Joules unit + witness", () => {
  it("records and totals energy with witnesses", () => {
    const { sessionId } = beginSession({ cpu:"A" });
    const r1 = recordPhase({ sessionId, phase:"dataset", j: 0.25 });
    const r2 = recordPhase({ sessionId, phase:"training", j: 0.75 });
    const fin = finishSession(sessionId);
    expect(r1.witness && r2.witness && fin.witness).toBeTruthy();
    expect(fin.totalJ).toBeCloseTo(1.0, 9);
  });
});
