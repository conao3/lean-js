import type { Obj } from "./object.ts"
import {
  asBytes,
  asCtor,
  asNat,
  asString,
  lean_apply,
  lean_bool,
  lean_ctor,
  lean_trampoline,
  lean_unbox,
} from "./object.ts"

const utf8enc = new TextEncoder()
const utf8dec = new TextDecoder("utf-8", { fatal: false })

export function encodeUtf8(s: string): Uint8Array {
  return utf8enc.encode(s)
}

export function decodeUtf8(b: Uint8Array): string {
  return utf8dec.decode(b)
}

// ---- Char ----
export function lean_char_to_nat(c: number): bigint {
  return BigInt(c)
}

// ---- String: UTF-8 / code-point semantics ----
export function lean_string_length(s: Obj): bigint {
  let n = 0
  for (const _ of asString(s)) n++
  return BigInt(n)
}

export function lean_string_append(a: Obj, b: Obj): string {
  return asString(a) + asString(b)
}

export function lean_string_push(s: Obj, c: number): string {
  return asString(s) + String.fromCodePoint(c)
}

export function lean_string_dec_eq(a: Obj, b: Obj): number {
  return lean_bool(a === b)
}

export function lean_string_isempty(s: Obj): number {
  return lean_bool(asString(s).length === 0)
}

// String.hash (extern lean_string_hash): MurmurHash64A over the UTF-8 bytes
// with seed 11, transcribed from the runtime's hash_str so bucket layout (and
// thus HashMap/HashSet iteration order) is bit-identical to the native backend.
const MURMUR_M = 0xc6a4a7935bd1e995n
const MURMUR_R = 47n

function wrap64(x: bigint): bigint {
  return BigInt.asUintN(64, x)
}

// mixHash (extern lean_uint64_mix_hash): the runtime's lean_uint64_mix_hash,
// used by Hashable for Prod/Option/Array/List and pointer hashing. Bit-exact.
export function lean_uint64_mix_hash(h0: bigint, k0: bigint): bigint {
  let k = wrap64(k0 * MURMUR_M)
  k ^= k >> MURMUR_R
  k ^= MURMUR_M
  let h = h0 ^ k
  h = wrap64(h * MURMUR_M)
  return wrap64(h)
}

export function lean_string_hash(s: Obj): bigint {
  const b = utf8enc.encode(asString(s))
  const len = b.length
  const m = MURMUR_M
  const r = MURMUR_R
  const at = (i: number): bigint => BigInt(b[i] ?? 0)
  let h = wrap64(11n ^ wrap64(BigInt(len) * m))
  const nblocks = (len / 8) | 0
  for (let i = 0; i < nblocks; i++) {
    let k = 0n
    for (let j = 0; j < 8; j++) k |= at(i * 8 + j) << BigInt(8 * j)
    k = wrap64(k * m)
    k ^= k >> r
    k = wrap64(k * m)
    h ^= k
    h = wrap64(h * m)
  }
  const t = nblocks * 8
  const rem = len & 7
  if (rem >= 7) h ^= at(t + 6) << 48n
  if (rem >= 6) h ^= at(t + 5) << 40n
  if (rem >= 5) h ^= at(t + 4) << 32n
  if (rem >= 4) h ^= at(t + 3) << 24n
  if (rem >= 3) h ^= at(t + 2) << 16n
  if (rem >= 2) h ^= at(t + 1) << 8n
  if (rem >= 1) {
    h ^= at(t)
    h = wrap64(h * m)
  }
  h ^= h >> r
  h = wrap64(h * m)
  h ^= h >> r
  return wrap64(h)
}

// String.data / String.toList -> List Char (code points): tag 0 = nil, tag 1 = cons{head,tail}
export function lean_string_data(s: Obj): Obj {
  return Array.from(asString(s)).reduceRight<Obj>(
    (tl, ch) => lean_ctor(1, 2, 0, 0, ch.codePointAt(0), tl),
    0,
  )
}

// String.mk : List Char -> String
export function lean_string_mk(lst: Obj): string {
  let out = ""
  let cur = lst
  while (typeof cur !== "number" && asCtor(cur).tag === 1) {
    const c = asCtor(cur)
    out += String.fromCodePoint(lean_unbox(c.fields[0]))
    cur = c.fields[1]
  }
  return out
}

// ---- String: UTF-8 byte-position layer (String.Pos == UTF-8 byte offset) ----
// Lean indexes the raw UTF-8 byte buffer, not JS UTF-16 units. Positions are
// byte offsets (bigint).

// utf8Size of a code point (matches Char.utf8Size).
function charUtf8Size(c: number): bigint {
  return c <= 0x7f ? 1n : c <= 0x7ff ? 2n : c <= 0xffff ? 3n : 4n
}

function isFirstByte(b: number): boolean {
  return (b & 0xc0) !== 0x80
}

function decodeAt(bytes: Uint8Array, i: number): [number, number] {
  const at = (k: number): number => bytes[k] ?? 0
  const c0 = at(i)
  if (c0 < 0x80) return [c0, 1]
  if (c0 < 0xe0) return [((c0 & 0x1f) << 6) | (at(i + 1) & 0x3f), 2]
  if (c0 < 0xf0) return [((c0 & 0x0f) << 12) | ((at(i + 1) & 0x3f) << 6) | (at(i + 2) & 0x3f), 3]
  return [
    ((c0 & 0x07) << 18) |
      ((at(i + 1) & 0x3f) << 12) |
      ((at(i + 2) & 0x3f) << 6) |
      (at(i + 3) & 0x3f),
    4,
  ]
}

function validPos(b: Uint8Array, i: number): boolean {
  return i >= 0 && i < b.length && isFirstByte(b[i] ?? 0)
}

// String.utf8ByteSize / rawEndPos.byteIdx
export function lean_string_utf8_byte_size(s: Obj): bigint {
  return BigInt(utf8enc.encode(asString(s)).length)
}

// String.get : char at byte pos p, or 'A' (U+0041) if mid-char / out of range.
export function lean_string_utf8_get(s: Obj, p: Obj): number {
  const b = utf8enc.encode(asString(s))
  const i = Number(asNat(p))
  if (!validPos(b, i)) return 0x41
  return decodeAt(b, i)[0]
}

// String.get! : same value (panics in Lean on bad pos; here returns default).
export function lean_string_utf8_get_bang(s: Obj, p: Obj): number {
  return lean_string_utf8_get(s, p)
}

// String.get? : some codepoint (tag 1) or none (tag 0).
export function lean_string_utf8_get_opt(s: Obj, p: Obj): Obj {
  const b = utf8enc.encode(asString(s))
  const i = Number(asNat(p))
  if (!validPos(b, i)) return 0
  return lean_ctor(1, 1, 0, 0, decodeAt(b, i)[0])
}

// String.next : advance byte offset by the char's UTF-8 size (1 at end/invalid).
export function lean_string_utf8_next(s: Obj, p: Obj): bigint {
  return asNat(p) + charUtf8Size(lean_string_utf8_get(s, p))
}

// String.prev : start byte of the char before p; prev(0)=0.
export function lean_string_utf8_prev(s: Obj, p: Obj): bigint {
  const b = utf8enc.encode(asString(s))
  let i = Number(asNat(p))
  if (i <= 0) return 0n
  if (i > b.length) return BigInt(i - 1)
  i -= 1
  while (i > 0 && !isFirstByte(b[i] ?? 0)) i -= 1
  return BigInt(i)
}

// String.atEnd : byteIdx >= utf8ByteSize.
export function lean_string_utf8_at_end(s: Obj, p: Obj): number {
  return lean_bool(Number(asNat(p)) >= utf8enc.encode(asString(s)).length)
}

// String.extract : copy bytes [b, e); "" if b>=e; e clamps to end.
export function lean_string_utf8_extract(s: Obj, lo: Obj, hi: Obj): string {
  const bytes = utf8enc.encode(asString(s))
  let a = Number(asNat(lo))
  let z = Number(asNat(hi))
  if (a >= z) return ""
  if (z > bytes.length) z = bytes.length
  if (a > z) a = z
  return utf8dec.decode(bytes.slice(a, z))
}

export function lean_string_utf8_extract_fast(s: Obj, lo: Obj, hi: Obj): string {
  return lean_string_utf8_extract(s, lo, hi)
}

// String.set : replace the char starting at byte pos p with codepoint c. A pos
// that is out of range or mid-char leaves the string unchanged (Lean returns s).
export function lean_string_utf8_set(s: Obj, p: Obj, c: number): string {
  const str = asString(s)
  const b = utf8enc.encode(str)
  const i = Number(asNat(p))
  if (!validPos(b, i)) return str
  const n = decodeAt(b, i)[1]
  return utf8dec.decode(b.slice(0, i)) + String.fromCodePoint(c) + utf8dec.decode(b.slice(i + n))
}

// String.posOf : byte pos of first occurrence of c, else utf8ByteSize.
export function lean_string_utf8_pos_of(s: Obj, c: number): bigint {
  const b = utf8enc.encode(asString(s))
  for (let i = 0; i < b.length;) {
    const [cp, n] = decodeAt(b, i)
    if (cp === c) return BigInt(i)
    i += n
  }
  return BigInt(b.length)
}

export function lean_string_contains(s: Obj, c: number): number {
  return lean_bool(Number(lean_string_utf8_pos_of(s, c)) !== utf8enc.encode(asString(s)).length)
}

// String.getUTF8Byte (extern lean_string_get_byte_fast): byte at byte offset p.
// The dependent `p < rawEndPos` proof arg is erased/dropped by the emitter.
export function lean_string_get_byte_fast(s: Obj, p: Obj): number {
  return utf8enc.encode(asString(s))[Number(asNat(p))] ?? 0
}

// String.decodeChar (extern lean_string_utf8_get_fast): decode the char whose
// UTF-8 sequence begins at byte offset; same decode as String.get.
export function lean_string_utf8_get_fast(s: Obj, p: Obj): number {
  return lean_string_utf8_get(s, p)
}

// String.Internal.isPrefixOf (extern lean_string_isprefixof): p, s -> Bool.
export function lean_string_isprefixof(p: Obj, s: Obj): number {
  return lean_bool(asString(s).startsWith(asString(p)))
}

// String.Internal.any (extern lean_string_any): apply the Char->Bool closure to
// each code point until one returns true (Bool scalar 1).
export function lean_string_any(s: Obj, p: Obj): number {
  for (const ch of asString(s)) if (lean_trampoline(lean_apply(p, [ch.codePointAt(0)]))) return 1
  return 0
}

// USize.repr / Nat.repr style decimal rendering.
export function lean_string_of_usize(a: bigint): string {
  return a.toString()
}

// String.toByteArray / toUTF8 (extern lean_string_to_utf8).
export function lean_string_to_utf8(s: Obj): Uint8Array {
  return utf8enc.encode(asString(s))
}

// String.ofByteArray / fromUTF8(!)/Unchecked (extern lean_string_from_utf8_unchecked).
export function lean_string_from_utf8_unchecked(b: Obj): string {
  return utf8dec.decode(asBytes(b))
}

// ByteArray.validateUTF8 (extern lean_string_validate_utf8): Bool scalar.
export function lean_string_validate_utf8(b: Obj): number {
  try {
    new TextDecoder("utf-8", { fatal: true }).decode(asBytes(b))
    return 1
  } catch {
    return 0
  }
}

// String.Pos.Raw.next' (extern lean_string_utf8_next_fast): the byte position
// after the char at p (p is in range and on a char boundary).
export function lean_string_utf8_next_fast(s: Obj, p: Obj): bigint {
  return lean_string_utf8_next(s, p)
}

// String.Internal.memcmpStr (extern lean_string_memcmp): do the len bytes of
// lhs at lstart equal those of rhs at rstart (both ranges are in bounds).
export function lean_string_memcmp(lhs: Obj, rhs: Obj, lstart: Obj, rstart: Obj, len: Obj): number {
  const a = utf8enc.encode(asString(lhs))
  const b = utf8enc.encode(asString(rhs))
  const l = Number(asNat(lstart))
  const r = Number(asNat(rstart))
  const n = Number(asNat(len))
  for (let i = 0; i < n; i++) if (a[l + i] !== b[r + i]) return 0
  return 1
}
