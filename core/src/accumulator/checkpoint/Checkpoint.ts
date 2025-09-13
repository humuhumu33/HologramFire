import { buildTree, proveInclusion, verifyInclusion, Hash } from "../merkle/Merkle";

export interface Checkpoint {
  round: number;
  shards: Hash[];   // per-shard roots in fixed order
  agg: Hash;        // merkle root over shards[]
}

export function makeCheckpoint(roots: Hash[], round: number): Checkpoint {
  const t = buildTree(roots);
  return { round, shards: roots.slice(), agg: t.root };
}

export interface ShardProof {
  shardIndex: number;
  proof: ReturnType<typeof proveInclusion>;
}

export function proveShard(ckpt: Checkpoint, shardIndex: number): ShardProof {
  if (shardIndex < 0 || shardIndex >= ckpt.shards.length) throw new Error("shard_index_oob");
  return { shardIndex, proof: proveInclusion(ckpt.shards, shardIndex) };
}

export function verifyShard(ckpt: Checkpoint, sp: ShardProof): boolean {
  return verifyInclusion(ckpt.agg, sp.proof)
    && ckpt.shards[sp.shardIndex] === (sp.proof.leaf as string);
}
