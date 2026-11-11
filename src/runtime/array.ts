import type { Obj } from "./object.ts"
import { asArray, asBytes, asCtor, asFloats, asNat, lean_ctor, lean_unbox } from "./object.ts"
import { lean_panic_fn } from "./io.ts"

// ---- ByteArray: a Uint8Array (matches IO read buffers). Setters copy, like
// Array, because the JS reference graph cannot honor Lean's uniqueness. ----
export function lean_mk_empty_byte_array(_cap: Obj): Uint8Array {
  return new Uint8Array(0)
}

export function lean_byte_array_size(a: Obj): bigint {
  return BigInt(asBytes(a).length)
}

export function lean_sarray_size(a: Obj): bigint {
  return BigInt(a instanceof Float64Array ? a.length : asBytes(a).length)
}

export function lean_byte_array_push(a: Obj, b: number): Uint8Array {
  const src = asBytes(a)
  const r = new Uint8Array(src.length + 1)
  r.set(src)
  r[src.length] = b & 0xff
  return r
}

// ByteArray.get! : byte at index; out-of-bounds panics in Lean, returns 0 here.
export function lean_byte_array_get(a: Obj, i: Obj): number {
  return asBytes(a)[Number(i)] ?? 0
}

export function lean_byte_array_fget(a: Obj, i: Obj): number {
  return asBytes(a)[Number(i)] ?? 0
}

export function lean_byte_array_uget(a: Obj, i: bigint): number {
  return asBytes(a)[Number(i)] ?? 0
}

export function lean_byte_array_set(a: Obj, i: Obj, b: number): Uint8Array {
  const src = asBytes(a)
  const j = Number(i)
  if (j < 0 || j >= src.length) return src
  const r = src.slice()
  r[j] = b & 0xff
  return r
}

export function lean_byte_array_fset(a: Obj, i: Obj, b: number): Uint8Array {
  return lean_byte_array_set(a, i, b)
}

export function lean_byte_array_uset(a: Obj, i: bigint, b: number): Uint8Array {
  return lean_byte_array_set(a, i, b)
}

// ByteArray.copySlice src srcOff dest destOff len exact : splice src[srcOff,+len)
// into dest at destOff, growing dest, exactly as the Lean Array-extract spec.
export function lean_byte_array_copy_slice(
  src: Obj,
  srcOff: Obj,
  dest: Obj,
  destOff: Obj,
  len: Obj,
  _exact: number,
): Uint8Array {
  const s = asBytes(src)
  const d = asBytes(dest)
  const so = Number(srcOff)
  const doff = Number(destOff)
  const n = Number(len)
  const take = Math.min(n, Math.max(0, s.length - so))
  const head = d.subarray(0, doff)
  const mid = s.subarray(so, so + take)
  const tail = d.subarray(doff + take)
  const r = new Uint8Array(head.length + mid.length + tail.length)
  r.set(head, 0)
  r.set(mid, head.length)
  r.set(tail, head.length + mid.length)
  return r
}

// ---- FloatArray: packed doubles -> Float64Array (mirrors ByteArray=Uint8Array).
// The C runtime stores packed `double`s in an sarray; Float64Array is the exact
// JS analog. Setters copy-on-write, like the Array/ByteArray externs, because JS
// arrays are reference-shared and the compiler's unique-assumed paths would
// otherwise corrupt the caller.
export function lean_float_array_mk(a: Obj): Float64Array {
  return Float64Array.from(asArray(a), lean_unbox)
}

export function lean_float_array_data(a: Obj): Obj[] {
  return Array.from(asFloats(a))
}

export function lean_copy_float_array(a: Obj): Float64Array {
  return asFloats(a).slice()
}

export function lean_mk_empty_float_array(_cap: Obj): Float64Array {
  return new Float64Array(0)
}

export function lean_float_array_size(a: Obj): bigint {
  return BigInt(asFloats(a).length)
}

export function lean_float_array_push(a: Obj, d: number): Float64Array {
  const src = asFloats(a)
  const r = new Float64Array(src.length + 1)
  r.set(src)
  r[src.length] = d
  return r
}

export function lean_float_array_uget(a: Obj, i: bigint): number {
  return asFloats(a)[Number(i)] ?? 0
}

export function lean_float_array_fget(a: Obj, i: Obj): number {
  return asFloats(a)[Number(i)] ?? 0
}

// FloatArray.get! : OOB returns 0.0 (matches lean.h lean_float_array_get).
export function lean_float_array_get(a: Obj, i: Obj): number {
  return asFloats(a)[Number(i)] ?? 0.0
}

export function lean_float_array_uset(a: Obj, i: bigint, d: number): Float64Array {
  const r = asFloats(a).slice()
  r[Number(i)] = d
  return r
}

export function lean_float_array_fset(a: Obj, i: Obj, d: number): Float64Array {
  const r = asFloats(a).slice()
  r[Number(i)] = d
  return r
}

// FloatArray.set! : OOB returns the array unchanged (matches lean.h).
export function lean_float_array_set(a: Obj, i: Obj, d: number): Float64Array {
  const src = asFloats(a)
  const j = Number(i)
  if (j < 0 || j >= src.length) return src
  const r = src.slice()
  r[j] = d
  return r
}

// ---- Array: JS array. get is bounds-checked w/ default. ----
export function lean_array_get_size(a: Obj): bigint {
  return BigInt(asArray(a).length)
}

export function lean_array_fget(a: Obj, i: Obj): Obj {
  return asArray(a)[Number(i)]
}

// Array.get!Internal (extern lean_array_get): the C signature passes the
// Inhabited default FIRST, then the array, then the index (a[i]! lowers here).
// Out of bounds routes through lean_array_get_panic, which calls lean_panic_fn
// with "Error: index out of bounds" -- it prints that message to stderr (subject
// to LEAN_BACKTRACE) and returns the Inhabited default, just like panic!.
export function lean_array_get(dflt: Obj, a: Obj, i: Obj): Obj {
  const arr = asArray(a)
  const idx = Number(i)
  return idx >= 0 && idx < arr.length ? arr[idx] : lean_panic_fn(dflt, "Error: index out of bounds")
}

// Array.get!InternalBorrowed (extern lean_array_get_borrowed): identical
// signature and semantics to lean_array_get; the only C-level difference is the
// borrowed-vs-owned refcount on `a`, which is a no-op in GC'd JS. The compiler
// emits this variant when the indexed element is only borrowed (e.g. a[i]!.size).
export function lean_array_get_borrowed(dflt: Obj, a: Obj, i: Obj): Obj {
  return lean_array_get(dflt, a, i)
}

export function lean_array_uget(a: Obj, i: bigint): Obj {
  return asArray(a)[Number(i)]
}

// Array.getInternalBorrowed (C lean_array_fget_borrowed) and Array.ugetBorrowed
// (C lean_array_uget_borrowed): the borrowed twins of fget/uget. The only
// C-level difference is the borrowed-vs-owned refcount on the returned element,
// which is a no-op in GC'd JS.
export function lean_array_fget_borrowed(a: Obj, i: Obj): Obj {
  return lean_array_fget(a, i)
}

export function lean_array_uget_borrowed(a: Obj, i: bigint): Obj {
  return lean_array_uget(a, i)
}

export function lean_array_propagate_mark(_src: Obj, dst: Obj): Obj {
  return dst
}

// Setters return a fresh array (functional), mirroring the ctor reuse/copy
// model: JS arrays are reference-shared with no refcount, so in-place updates
// from the compiler's unsafe (assumed-unique) map/foldl paths would corrupt the
// caller's array. Copying keeps Array semantics pure and aliases intact.
export function lean_array_set(a: Obj, i: Obj, v: Obj): Obj[] {
  const b = asArray(a).slice()
  b[Number(i)] = v
  return b
}

export function lean_array_push(a: Obj, v: Obj): Obj[] {
  const b = asArray(a).slice()
  b.push(v)
  return b
}

export function lean_array_pop(a: Obj): Obj[] {
  const b = asArray(a).slice()
  b.pop()
  return b
}

export function lean_array_swap(a: Obj, i: Obj, j: Obj): Obj[] {
  const b = asArray(a).slice()
  const x = Number(i)
  const y = Number(j)
  ;[b[x], b[y]] = [b[y], b[x]]
  return b
}

export function lean_array_uset(a: Obj, i: bigint, v: Obj): Obj[] {
  const b = asArray(a).slice()
  b[Number(i)] = v
  return b
}

export function lean_array_usize(a: Obj): bigint {
  return BigInt(asArray(a).length)
}

export function lean_mk_array(n: Obj, v: Obj): Obj[] {
  return Array.from<Obj>({ length: Number(asNat(n)) }).fill(v)
}

// Array.toList -> List (tag 0 = nil, tag 1 = cons{head, tail}).
export function lean_array_to_list(a: Obj): Obj {
  return asArray(a).reduceRight<Obj>((tl, h) => lean_ctor(1, 2, 0, 0, h, tl), 0)
}

// Array.mk : List a -> Array a (the IR ctor for the Array's backing buffer).
export function lean_array_mk(lst: Obj): Obj[] {
  const out: Obj[] = []
  let cur = lst
  while (typeof cur !== "number" && asCtor(cur).tag === 1) {
    const c = asCtor(cur)
    out.push(c.fields[0])
    cur = c.fields[1]
  }
  return out
}
