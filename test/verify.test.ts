import { describe, expect, test } from "vite-plus/test"
import * as calc from "./verify/app/src/calc.ts"
import * as spec from "./verify/app/src/_lean/calc.ts"
import { checkModel, checkModule, model, PropertyFailure } from "../src/verify/index.ts"

function badClamp(x: number, lo: number, _hi: number): number {
  return Math.max(lo, x)
}

model(badClamp, { refines: spec.clampSpec, requires: spec.ordered })

function badSum(xs: readonly number[]): number {
  let total = 0
  for (const x of xs) total += x
  return total
}

model(badSum, { ensures: { nonneg: spec.nonneg } })

function identity(x: number): number {
  return x
}

model(identity, { refines: (x: number) => x })

describe("checkModel", () => {
  test("the fixture functions agree with their specifications", async () => {
    await checkModel(calc.clamp)
    await checkModel(calc.firstOr)
    await checkModel(calc.sumAbs)
    await checkModel(calc.twice)
    await checkModel(calc.sumTo, { range: { min: 0n, max: 200n }, numRuns: 50 })
  })

  test("checkModule runs every model function of a module", async () => {
    await checkModule(calc, { range: { min: -300n, max: 300n }, numRuns: 30 })
  })

  test("a wrong implementation fails with a counterexample", async () => {
    const err: unknown = await checkModel(badClamp).catch((e: unknown) => e)
    expect(err).toBeInstanceOf(PropertyFailure)
    expect(String(err)).toMatch(/Counterexample/u)
    expect(String(err)).toMatch(/badClamp\[.*\] = .*, the spec gives /u)
  })

  test("a broken postcondition names its label", async () => {
    const err: unknown = await checkModel(badSum).catch((e: unknown) => e)
    expect(String(err)).toMatch(/breaks nonneg/u)
  })

  test("a specification must come from a lean(...) block", async () => {
    await expect(checkModel(identity)).rejects.toThrow(/not a function of a lean/u)
  })

  test("a function without model(...) is rejected", async () => {
    await expect(checkModel((x: number) => x)).rejects.toThrow(/has no model/u)
  })
})
