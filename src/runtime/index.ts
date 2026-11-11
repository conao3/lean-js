import { setPlatform } from "./io.ts"
import { nodePlatform } from "./node.ts"

export * from "./object.ts"
export * from "./nat.ts"
export * from "./int.ts"
export * from "./uint.ts"
export * from "./float.ts"
export * from "./string.ts"
export * from "./array.ts"
export * from "./io.ts"
export * from "./marshal.ts"
export * from "./block.ts"
export {
  type ExceptInput,
  type InferInput,
  type InferOutput,
  type LeanSchema,
  merge,
  schema,
  type UnitInput,
} from "../schema/index.ts"

if (typeof process !== "undefined" && typeof process.getBuiltinModule === "function")
  setPlatform(nodePlatform())
