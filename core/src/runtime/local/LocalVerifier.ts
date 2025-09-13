import { VpiRegistry, VerifyResult, estimateCost, makeWitness } from "../vpi/VPI";
import { proofFromBudgets, verifyProof } from "../../logic/proof/Proof";
import { SessionVerifier, Frame } from "../../transport/ctp96/CTP96";

export interface ModuleVerifyRequest {
  moduleId: string;
  input: unknown;
  budgets?: number[];   // optional – if provided, must sum to 0 mod 96
}

export class LocalVerifier {
  constructor(private vpi: VpiRegistry) {}

  /** Verify a stream of transport frames using the session state machine. */
  verifyTransport(frames: Frame[]): VerifyResult {
    const sv = new SessionVerifier();
    for (const f of frames) sv.verify(f);
    const cost = { cycles: frames.length, pages: 1 };
    const witness = makeWitness("ctp96.session", frames.map(f => ({ kind: f.kind, seq: f.seq, nonce: f.nonce })));
    return { ok: true, cost, witness };
  }

  /** Verify a module request using its registered plugin and optional proof budget. */
  async verifyModule(req: ModuleVerifyRequest): Promise<VerifyResult> {
    // Enforce budgets if provided (fail-closed)
    if (req.budgets && !verifyProof(proofFromBudgets(req.budgets))) {
      return { ok: false, reason: "budget_invalid", cost: { cycles: 0, pages: 0 } };
    }
    const plugin = this.vpi.get(req.moduleId);
    const res = await plugin.verify(req.input, { budget: req.budgets });
    // Post-condition: must include cost; attach witness if missing
    const cost = res.cost ?? estimateCost(req.input);
    const witness = res.witness ?? makeWitness("vpi.verify", { module: req.moduleId, input: req.input });
    return { ok: res.ok, reason: res.reason, cost, witness };
  }
}
