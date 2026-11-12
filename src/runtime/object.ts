// Representation choices:
//   Nat  -> bigint (>= 0n)        Int   -> bigint
//   UInt8/16/32, Int8/16/32 -> number (the unsigned bit pattern, as lean.h stores int8_t in uint8_t)
//   UInt64/USize -> bigint        Int64/ISize -> bigint (two's complement, normalized by every op)
//   Float/Float32 -> number       Bool -> scalar 0/1   Char -> number (code point)
//   String -> JS string; String.Pos is a UTF-8 byte offset
//   Array<T> -> Obj[]             List<T> -> tagged ctor objects {tag, fields}
// Bool is lowered to a scalar (false=0, true=1) matched by the emitted
// `switch`, so decEq/decLt/decLe and other Bool-returning externs return the
// number 0 or 1 (NOT a JS boolean: `switch (true)` would not hit `case 1`).

import { WORD_BITS } from "./uint.ts"

export type Fn = (...args: never[]) => unknown

export interface Ctor {
  tag: number
  fields: Obj[]
  sdata: DataView | null
}

export interface Closure {
  fn: Fn
  arity: number
  args: Obj[]
}

export interface Ref {
  value: Obj
}

export interface Handle {
  fd: number
}

export interface Thunk {
  closure: Obj
  forced: boolean
  result: Obj
}

export type Obj =
  | Ctor
  | Closure
  | Ref
  | Handle
  | Thunk
  | Fn
  | bigint
  | number
  | string
  | Obj[]
  | Uint8Array
  | Float64Array
  | null
  | undefined

export type Bounce = { tc: 1; f: Fn; a: Obj[] } | { tc: 2; clo: Obj; a: Obj[] }

function fail(what: string, x: unknown): never {
  throw new TypeError(`lean-ts runtime: expected ${what}, got ${typeof x}`)
}

export function lean_bool(b: boolean): number {
  return b ? 1 : 0
}

export function asCtor(x: Obj): Ctor {
  if (typeof x === "object" && x !== null && "tag" in x) return x
  return fail("a constructor object", x)
}

export function asClosure(x: Obj): Closure {
  if (typeof x === "object" && x !== null && "arity" in x) return x
  return fail("a closure", x)
}

export function asRef(x: Obj): Ref {
  if (typeof x === "object" && x !== null && "value" in x) return x
  return fail("a reference", x)
}

export function asHandle(x: Obj): Handle {
  if (typeof x === "object" && x !== null && "fd" in x) return x
  return fail("a file handle", x)
}

export function asNat(x: Obj): bigint {
  if (typeof x === "bigint") return x
  return fail("a bigint", x)
}

export function asString(x: Obj): string {
  if (typeof x === "string") return x
  return fail("a string", x)
}

export function asArray(x: Obj): Obj[] {
  if (Array.isArray(x)) return x
  return fail("an array", x)
}

export function asBytes(x: Obj): Uint8Array {
  if (x instanceof Uint8Array) return x
  return fail("a Uint8Array", x)
}

export function asFloats(x: Obj): Float64Array {
  if (x instanceof Float64Array) return x
  return fail("a Float64Array", x)
}

export function lean_unbox(x: Obj): number {
  if (typeof x === "number") return x
  return fail("a number", x)
}

export function lean_unbox_uint64(x: Obj): bigint {
  return asNat(x)
}

// Constructor tag of a value. Nullary ctors of a multi-ctor inductive (e.g.
// List.nil, Bool.false) are lowered to the bare number cidx (like lean_box);
// ctors with fields are objects { tag, fields }. lean_obj_tag handles both.
export function lean_tag(x: Obj): number {
  return typeof x === "number" ? x : asCtor(x).tag
}

// ---- constructor objects: three regions mirroring lean_alloc_ctor ----
// A heap ctor is one block with header + object/usize word slots + packed
// scalar bytes (Lean.Compiler.IR.Basic CtorInfo {size, usize, ssize}):
//   fields : word slots. fields[0..size) are object pointers (proj/set),
//            fields[size..size+usize) are USize values (uproj/uset). Both use
//            the IR word index directly, exactly as lean_ctor_get / _get_usize.
//   sdata  : a DataView of `ssize` packed scalar bytes (sproj/sset), addressed
//            by byte offset (the IR's word-prefix `n` is dropped; sdata starts
//            at its own offset 0). Little-endian to match native x86_64.
// A fully-scalar ctor (size==usize==ssize==0) is a bare number cidx (lean_box).
export function lean_alloc_ctor(tag: number, size: number, usize: number, ssize: number): Ctor {
  return {
    tag,
    fields: Array.from<Obj>({ length: size + usize }),
    sdata: ssize > 0 ? new DataView(new ArrayBuffer(ssize)) : null,
  }
}

// Allocate a ctor and fill its object region positionally (mirrors emitCtor +
// emitCtorSetArgs); usize/scalar fields are filled later by uset/sset.
export function lean_ctor(
  tag: number,
  size: number,
  usize: number,
  ssize: number,
  ...objs: Obj[]
): Ctor {
  const c = lean_alloc_ctor(tag, size, usize, ssize)
  for (let i = 0; i < objs.length; i++) c.fields[i] = objs[i]
  return c
}

export function lean_ctor_get(x: Obj, i: number): Obj {
  return asCtor(x).fields[i]
}

export function lean_ctor_set(x: Obj, i: number, v: Obj): void {
  asCtor(x).fields[i] = v
}

export function lean_ctor_set_tag(x: Obj, tag: number): void {
  asCtor(x).tag = tag
}

export function lean_ctor_uget(x: Obj, i: number): bigint {
  return asNat(asCtor(x).fields[i])
}

export function lean_ctor_uset(x: Obj, i: number, v: bigint): void {
  asCtor(x).fields[i] = v
}

function sdata(x: Obj): DataView {
  const d = asCtor(x).sdata
  if (d === null) return fail("a constructor with scalar fields", x)
  return d
}

// Packed-scalar get/set into region S (sproj/sset), byte offset addressed,
// width chosen by IR type. u8/u16/u32 -> number; u64/usize -> bigint; floats
// -> number. Little-endian to match the native ABI.
export function lean_ctor_get_u8(x: Obj, o: number): number {
  return sdata(x).getUint8(o)
}

export function lean_ctor_get_u16(x: Obj, o: number): number {
  return sdata(x).getUint16(o, true)
}

export function lean_ctor_get_u32(x: Obj, o: number): number {
  return sdata(x).getUint32(o, true)
}

export function lean_ctor_get_u64(x: Obj, o: number): bigint {
  return sdata(x).getBigUint64(o, true)
}

export function lean_ctor_get_f64(x: Obj, o: number): number {
  return sdata(x).getFloat64(o, true)
}

export function lean_ctor_get_f32(x: Obj, o: number): number {
  return sdata(x).getFloat32(o, true)
}

export function lean_ctor_set_u8(x: Obj, o: number, v: number): void {
  sdata(x).setUint8(o, v & 0xff)
}

export function lean_ctor_set_u16(x: Obj, o: number, v: number): void {
  sdata(x).setUint16(o, v & 0xffff, true)
}

export function lean_ctor_set_u32(x: Obj, o: number, v: number): void {
  sdata(x).setUint32(o, v >>> 0, true)
}

export function lean_ctor_set_u64(x: Obj, o: number, v: bigint): void {
  sdata(x).setBigUint64(o, BigInt.asUintN(64, v), true)
}

export function lean_ctor_set_f64(x: Obj, o: number, v: number): void {
  sdata(x).setFloat64(o, v, true)
}

export function lean_ctor_set_f32(x: Obj, o: number, v: number): void {
  sdata(x).setFloat32(o, Math.fround(v), true)
}

// Packed USize scalar: width follows WORD_BITS (the pointer width), not a literal
// 64 — a 32-bit profile reads/writes 4 bytes. (In practice usize fields use the
// word-indexed uproj/uset path, not sproj/sset, so this is a defensive fallback.)
export function lean_ctor_get_usize(x: Obj, o: number): bigint {
  return WORD_BITS === 64 ? sdata(x).getBigUint64(o, true) : BigInt(sdata(x).getUint32(o, true))
}

export function lean_ctor_set_usize(x: Obj, o: number, v: bigint): void {
  if (WORD_BITS === 64) sdata(x).setBigUint64(o, BigInt.asUintN(64, v), true)
  else sdata(x).setUint32(o, Number(BigInt.asUintN(32, v)), true)
}

// ---- trampoline driver for mutual / cross-function tail calls ----
// A trampolined core returns a thunk { tc:1, f, a:[args] } at an SCC-internal
// tail edge instead of recursing; the driver unrolls thunks so no JS stack
// frame is consumed per tail step. Ordinary return values (ctors, bigints,
// numbers, strings, arrays, closures) never carry `tc`, so they pass through.
function isBounce(x: unknown): x is Bounce {
  return typeof x === "object" && x !== null && "tc" in x
}

export function lean_trampoline(t: Obj | Bounce): Obj {
  let cur = t
  while (isBounce(cur)) {
    // `tc:2` is a tail-position closure application (emitted for a tail `.ap`):
    // bounce it through lean_apply, which itself returns a `tc:1`/`tc:2` thunk
    // for its final saturating step, so the apply chain unrolls in constant stack.
    cur = cur.tc === 1 ? Reflect.apply(cur.f, undefined, cur.a) : lean_apply(cur.clo, cur.a)
  }
  return cur
}

// ---- closure application (pap/ap model) ----
// A closure value records the worker's FULL arity so apply can do the C runtime's
// three-way dispatch (Lean's lean_apply_n): exact, under (accumulate into a new
// closure), and over (saturate, then re-apply the result to the leftover args).
// pap c ys -> lean_closure(<funRef c>, ARITY, [ys...]) where ARITY is c's full
// IR arity (the param count emitted for funRef c), so apply can branch on
// (arity - args.length) vs the number of args supplied. An arity of -1 marks a
// closure whose worker arity is unknown: it is applied by a single concat-and-call.
export function lean_closure(fn: Fn, arity: number, args: Obj[]): Closure {
  return { fn, arity, args }
}

// Returns a `tc:1` thunk for the FINAL saturating worker call instead of
// calling it directly, so when reached through the trampoline (a tail `.ap`'s
// `tc:2` thunk, or the wrapped non-tail site below) the driver makes the call
// in constant stack — flattening CPS / continuation tail loops. Intermediate
// over-application steps must force the result NOW to know how to re-apply the
// leftover args; that forcing is bounded by the static curry depth, not by the
// loop iteration count, so it does not grow the stack per iteration.
export function lean_apply(clo: Obj, more: Obj[]): Obj | Bounce {
  // Bare JS function: treat as a fully-applied call (IR wraps fn values in pap,
  // but FS.Stream fields and other runtime closures are bare functions).
  if (typeof clo === "function") return { tc: 1, f: clo, a: more }
  let cur = asClosure(clo)
  if (cur.arity < 0) return { tc: 1, f: cur.fn, a: cur.args.concat(more) }
  let i = 0
  while (i < more.length) {
    const need = cur.arity - cur.args.length
    const avail = more.length - i
    if (avail < need) {
      return lean_closure(cur.fn, cur.arity, cur.args.concat(more.slice(i)))
    }
    const callArgs = cur.args.concat(more.slice(i, i + need))
    i += need
    if (i === more.length) return { tc: 1, f: cur.fn, a: callArgs }
    const res = lean_trampoline({ tc: 1, f: cur.fn, a: callArgs })
    if (typeof res === "function") return { tc: 1, f: res, a: more.slice(i) }
    const next = asClosure(res)
    if (next.arity < 0) return { tc: 1, f: next.fn, a: next.args.concat(more.slice(i)) }
    cur = next
  }
  return cur
}

export function asThunk(x: Obj): Thunk {
  if (typeof x === "object" && x !== null && "forced" in x) return x
  return fail("a thunk", x)
}

export function lean_mk_thunk(c: Obj): Thunk {
  return { closure: c, forced: false, result: undefined }
}

export function lean_thunk_pure(v: Obj): Thunk {
  return { closure: null, forced: true, result: v }
}

export function lean_thunk_get(x: Obj): Obj {
  const t = asThunk(x)
  if (t.forced) return t.result
  const c = t.closure
  if (c === null) throw new TypeError("lean-ts runtime: a thunk forced itself")
  t.closure = null
  t.result = lean_trampoline(lean_apply(c, [0]))
  t.forced = true
  return t.result
}

export function lean_thunk_get_own(x: Obj): Obj {
  return lean_thunk_get(x)
}
