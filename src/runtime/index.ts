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

if (typeof process !== "undefined" && typeof process.getBuiltinModule === "function")
  setPlatform(nodePlatform())
