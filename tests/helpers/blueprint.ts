import fs from "node:fs";
import os from "node:os";
import path from "node:path";

export const realBlueprintPath = path.resolve("atlas-12288/blueprint/blueprint.json");
export const realBlueprintSchemaPath = path.resolve("atlas-12288/blueprint/blueprint.schema.json");

/** Make a temp clone of the canonical blueprint, optionally merging `modulesPatch`. */
export function cloneBlueprint(modulesPatch?: Record<string, any>) {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "atlas-12288-"));
  const tmpBlueprint = path.join(tmpDir, "blueprint.json");
  const tmpBlueprintSchema = path.join(tmpDir, "blueprint.schema.json");
  
  // Copy the blueprint.json with optional module patches
  const obj = JSON.parse(fs.readFileSync(realBlueprintPath, "utf8"));
  if (modulesPatch) obj.modules = { ...(obj.modules || {}), ...modulesPatch };
  fs.writeFileSync(tmpBlueprint, JSON.stringify(obj, null, 2));
  
  // Copy the blueprint.schema.json file
  fs.copyFileSync(realBlueprintSchemaPath, tmpBlueprintSchema);
  
  return { tmpDir, tmpBlueprint };
}
