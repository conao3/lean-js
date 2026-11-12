import { closeSync, openSync } from "node:fs"
import { isatty } from "node:tty"
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

describe("thunks", () => {
  test("a thunk runs its closure once and keeps the result", () => {
    let runs = 0
    const t = L.lean_mk_thunk(
      L.lean_closure(
        () => {
          runs += 1
          return 7n
        },
        1,
        [],
      ),
    )
    expect(L.lean_thunk_get_own(t)).toBe(7n)
    expect(L.lean_thunk_get(t)).toBe(7n)
    expect(runs).toBe(1)
    expect(L.lean_thunk_get(L.lean_thunk_pure("v"))).toBe("v")
  })

  test("a thunk that forces itself is a TypeError", () => {
    const t: L.Obj = L.lean_mk_thunk(L.lean_closure(() => L.lean_thunk_get(t), 1, []))
    expect(() => L.lean_thunk_get(t)).toThrow(TypeError)
  })
})

function streamIsTty(stream: L.Obj): L.Obj {
  return L.lean_trampoline(L.lean_apply(L.lean_ctor_get(stream, 5), [undefined]))
}

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

  test("the std streams and handles ask the platform about their own fd", () => {
    L.setPlatform({ ...L.browserPlatform, isTty: (fd) => fd === 1 })
    expect(streamIsTty(L.lean_get_stdin())).toBe(0)
    expect(streamIsTty(L.lean_get_stdout())).toBe(1)
    expect(streamIsTty(L.lean_get_stderr())).toBe(0)
    expect(L.lean_io_prim_handle_is_tty({ fd: 1 })).toBe(1)
    expect(L.lean_io_prim_handle_is_tty({ fd: 2 })).toBe(0)
    L.setPlatform({ ...L.browserPlatform, isTty: (fd) => fd === 2 })
    expect(streamIsTty(L.lean_get_stdout())).toBe(0)
    expect(streamIsTty(L.lean_get_stderr())).toBe(1)
  })

  test("the Node platform answers isatty for each fd", () => {
    for (const fd of [0, 1, 2]) expect(nodePlatform.isTty(fd)).toBe(isatty(fd))
    const fd = openSync("package.json", "r")
    try {
      expect(nodePlatform.isTty(fd)).toBe(false)
    } finally {
      closeSync(fd)
    }
    expect(nodePlatform.isTty(9999)).toBe(false)
  })
})

describe("models", () => {
  test("a model whose validate returns a Promise is a TypeError", () => {
    const struct = L.typeDesc({
      kind: "struct",
      name: "M",
      trivial: 0,
      variant: {
        name: "mk",
        cidx: 0,
        size: 1,
        usize: 0,
        ssize: 0,
        positional: false,
        fields: [
          {
            key: "n",
            desc: L.natDesc,
            slot: "obj",
            at: 0,
            omitNone: false,
            flat: false,
            bounds: {},
          },
        ],
        invariants: [],
      },
    })
    L.blockRegistry().models.set("test:Async", {
      "~standard": { version: 1, vendor: "test", validate: async (value: unknown) => ({ value }) },
    })
    expect(() => L.toLean(L.modelDesc("test:Async", "Async", struct), { n: 1 }, "m")).toThrow(
      "the model's ~standard.validate returned a Promise",
    )
    expect(() => L.toLean(L.modelDesc("test:Missing", "Missing", struct), { n: 1 }, "m")).toThrow(
      "the model Missing (test:Missing) is not registered",
    )
  })
})
