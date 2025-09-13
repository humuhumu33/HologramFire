import { describe, it, expect } from "vitest";
import { buildTree } from "../src/accumulator/merkle/Merkle";
import { makeCheckpoint, proveShard, verifyShard } from "../src/accumulator/checkpoint/Checkpoint";

describe("G9: Cross-shard checkpoints", () => {
  it("commits shard roots and proves inclusion of a shard", () => {
    const shard0 = buildTree([1,2,3]).root;
    const shard1 = buildTree(["x","y"]).root;
    const shard2 = buildTree([{a:1}]).root;
    const ckpt = makeCheckpoint([shard0, shard1, shard2], 42);
    const sp = proveShard(ckpt, 1);
    expect(verifyShard(ckpt, sp)).toBe(true);
  });
});
