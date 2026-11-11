import { afterEach, describe, expect, test } from "vite-plus/test"
import * as L from "../src/runtime/index.ts"

const nodePlatform = L.getPlatform()

afterEach(() => {
  L.setPlatform(nodePlatform)
})

describe("signed fixed-width ints", () => {
  test("Int8 is the unsigned bit pattern", () => {
    expect(L.lean_int8_of_int(-5n)).toBe(251)
    expect(L.lean_int8_to_int(251)).toBe(-5n)
    expect(L.lean_int8_to_int(L.lean_int8_add(L.lean_int8_of_int(127n), 1))).toBe(-128n)
  })

  test("Int64 normalizes an unsigned pattern read back from a packed field", () => {
    expect(L.lean_int64_dec_lt(2n ** 64n - 5n, -3n)).toBe(1)
  })
})

function add(a: L.Obj, b: L.Obj): bigint {
  return L.lean_nat_add(a, b)
}

describe("trampoline", () => {
  test("unrolls direct and apply thunks", () => {
    const clo = L.lean_closure(add, 2, [1n])
    expect(L.lean_trampoline({ tc: 2, clo, a: [2n] })).toBe(3n)
    expect(L.lean_trampoline({ tc: 1, f: add, a: [4n, 5n] })).toBe(9n)
  })
})

describe("platform", () => {
  test("OS operations return IO.Error.unsupportedOperation without Node", () => {
    L.setPlatform(L.browserPlatform)
    const res = L.lean_io_prim_handle_mk("input.txt", 0)
    expect(L.lean_io_result_is_ok(res)).toBe(false)
    const err = L.lean_io_result_get_error(res)
    expect(L.lean_tag(err)).toBe(4)
    expect(L.lean_io_error_to_string(err)).toBe(
      "unsupported operation (error code: 0, opening a file is not supported on browser)",
    )
  })
})
