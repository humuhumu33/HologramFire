export function stableStringify(obj: any): string {
  const norm = (v: any): any => {
    if (Array.isArray(v)) return v.map(norm).sort();
    if (v && typeof v === "object") {
      return Object.keys(v).sort().reduce((acc: any, k) => {
        if (k === "$comment") return acc; // ignore annotation
        acc[k] = norm(v[k]);
        return acc;
      }, {});
    }
    return v;
  };
  return JSON.stringify(norm(obj));
}
