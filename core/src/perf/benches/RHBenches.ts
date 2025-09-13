import { bench, PerfResult } from "../harness/Bench";
import { align } from "../../rh/Align";
import { skew } from "../../rh/Skew";
import { alphaBank } from "../../rh/Constants";
import { mirrorOf } from "../../rh/Mirror";

// Deterministic test vectors for RH benchmarks
const flatScores = Array(96).fill(1.0);
const mirrorPairScores = Array(96).fill(0);
for (let i = 0; i < 48; i++) {
  mirrorPairScores[i] = 1.0;
  mirrorPairScores[mirrorOf(i)] = 1.0;
}
const nearTieScores = Array(96).fill(0.5);
nearTieScores[0] = 0.501; // slight preference for class 0

export async function benchRhAlign(iters = 200): Promise<PerfResult> {
  return bench("rh.align", iters, () => {
    // Test different alignment scenarios
    align(flatScores, { tolerance: 1e-9 });
    align(mirrorPairScores, { tolerance: 1e-9 });
    align(nearTieScores, { tolerance: 1e-9 });
  });
}

export async function benchRhSkew(iters = 200): Promise<PerfResult> {
  return bench("rh.skew", iters, () => {
    // Test skew computation for different classes
    skew(flatScores, 0);
    skew(mirrorPairScores, 10);
    skew(nearTieScores, 24); // test a fixed point
  });
}

export async function benchRhConstants(iters = 200): Promise<PerfResult> {
  return bench("rh.constants", iters, () => {
    alphaBank();
  });
}

export async function benchRhMirror(iters = 200): Promise<PerfResult> {
  return bench("rh.mirror", iters, () => {
    // Test mirror operations
    for (let k = 0; k < 96; k += 8) { // sample every 8th class
      mirrorOf(k);
    }
  });
}
