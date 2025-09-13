import crypto from "node:crypto";
import { stableStringify } from "../../crypto/util/stable";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export type Hash = string;

function sha256(s: string): Hash {
  return crypto.createHash("sha256").update(s).digest("hex");
}

export function leafHash(v: unknown): Hash {
  // Domain-separated + canonical: resistant to structural ambiguity
  return ccmHash(stableStringify(v), "merkle.leaf");
}

export function nodeHash(left: Hash, right: Hash): Hash {
  return sha256("node|" + left + "|" + right);
}

export interface MerkleTree {
  leaves: Hash[];
  layers: Hash[][]; // layers[0] = leaves, last layer has length 1 (root)
  root: Hash;
}

export function buildTree(values: unknown[]): MerkleTree {
  const leaves = values.map(leafHash);
  const layers: Hash[][] = [];
  layers.push(leaves);

  let level = leaves;
  while (level.length > 1) {
    const next: Hash[] = [];
    for (let i = 0; i < level.length; i += 2) {
      const L = level[i];
      const R = i + 1 < level.length ? level[i + 1] : level[i]; // duplicate last if odd
      next.push(nodeHash(L, R));
    }
    layers.push(next);
    level = next;
  }
  const root = layers[layers.length - 1][0] ?? sha256("empty");
  return { leaves, layers, root };
}

export type Dir = "L" | "R";
export interface InclusionStep { dir: Dir; hash: Hash; }
export interface InclusionProof {
  index: number;
  leaf: unknown;
  path: InclusionStep[];
}

export function proveInclusion(values: unknown[], index: number): InclusionProof {
  const tree = buildTree(values);
  if (index < 0 || index >= tree.leaves.length) throw new Error("index_out_of_range");

  const path: InclusionStep[] = [];
  let i = index;
  for (let level = 0; level < tree.layers.length - 1; level++) {
    const layer = tree.layers[level];
    const isRight = i % 2 === 1;
    const sibIndex = isRight ? i - 1 : i + 1;
    const sibHash = layer[sibIndex] ?? layer[i]; // duplicate rule
    path.push({ dir: isRight ? "L" : "R", hash: sibHash });
    i = Math.floor(i / 2);
  }
  return { index, leaf: values[index], path };
}

export function verifyInclusion(root: Hash, proof: InclusionProof): boolean {
  let acc = leafHash(proof.leaf);
  for (const step of proof.path) {
    acc = step.dir === "L" ? nodeHash(step.hash, acc) : nodeHash(acc, step.hash);
  }
  return acc === root;
}

/** Exclusion by order-bounds:
 * For a sorted array of unique string keys, non-inclusion of target `k`
 * is proven by inclusion of predecessor and/or successor that bound `k`.
 */
export interface ExclusionProof {
  target: string;
  prev?: InclusionProof;  // proof for greatest key < target
  next?: InclusionProof;  // proof for least key > target
}
export function proveExclusion(keysSorted: string[], target: string): ExclusionProof {
  const tree = buildTree(keysSorted);
  const i = keysSorted.indexOf(target);
  if (i !== -1) throw new Error("target_is_present");
  // find predecessor and successor
  let p = -1, n = -1;
  for (let k = 0; k < keysSorted.length; k++) {
    if (keysSorted[k] < target) p = k;
    if (keysSorted[k] > target) { n = k; break; }
  }
  return {
    target,
    prev: p >= 0 ? proveInclusion(keysSorted, p) : undefined,
    next: n >= 0 ? proveInclusion(keysSorted, n) : undefined
  };
}
export function verifyExclusion(root: Hash, keysSorted: string[], proof: ExclusionProof): boolean {
  // Must have at least one bound; validate inclusion proofs
  if (!proof.prev && !proof.next) return false;
  if (proof.prev && !verifyInclusion(root, proof.prev)) return false;
  if (proof.next && !verifyInclusion(root, proof.next)) return false;
  // check ordering constraint
  const prevKey = proof.prev?.leaf as string | undefined;
  const nextKey = proof.next?.leaf as string | undefined;
  if (prevKey !== undefined && !(prevKey < proof.target)) return false;
  if (nextKey !== undefined && !(proof.target < nextKey)) return false;
  // and ensure target isn't actually present (belt-and-suspenders)
  return keysSorted.indexOf(proof.target) === -1;
}
