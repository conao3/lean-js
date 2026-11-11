// 32-bit USize profile: WORD_BITS is the single knob that routes the usize
// arithmetic width, System.Platform.getNumBits, the UInt64->USize truncation,
// and the packed-usize ctor slot size. Flip it to 32 in a copy of the runtime and
// assert that USize wraps at 2^32 and getNumBits reports 32. Real `lean` on this
// 64-bit host cannot serve as the oracle for a 32-bit target (cross-compilation
// is out of scope), so the 32-bit profile is checked against hand-computed
// literals; the 64-bit profile is the one the native oracle (oracle-vectors) covers.
import { cpSync, mkdirSync, readFileSync, writeFileSync } from "node:fs"

const show = (x) => String(x)

// Copy the runtime (with the schema module it re-exports) and the generated vectors module into test-out/usize32/,
// flipping the knob in the copy and pointing the module at the copied runtime.
const root = new URL("../../", import.meta.url)
const dir = new URL("test-out/usize32/", root)
mkdirSync(dir, { recursive: true })
cpSync(new URL("src/runtime/", root), new URL("runtime/", dir), { recursive: true })
cpSync(new URL("src/schema/", root), new URL("schema/", dir), { recursive: true })
const uintUrl = new URL("runtime/uint.ts", dir)
const knob = "export const WORD_BITS: number = 64"
const uint = readFileSync(uintUrl, "utf8")
if (!uint.includes(knob)) {
  console.error("USIZE32 FAIL: WORD_BITS knob not found in the runtime")
  process.exit(1)
}
writeFileSync(uintUrl, uint.replace(knob, "export const WORD_BITS: number = 32"))
const vectors = readFileSync(new URL("test-out/vectors.ts", root), "utf8").replaceAll(
  '"../src/runtime/index.ts"',
  '"./runtime/index.ts"',
)
writeFileSync(new URL("vectors.ts", dir), vectors)

const m = await import(new URL("vectors.ts", dir).href)
const nbits = m.l_LeanTsTest_Vectors_nbits
const uszOfU64 = m.l_LeanTsTest_Vectors_uszOfU64
const uszAdd = m.l_LeanTsTest_Vectors_uszAdd
const uszCompl = m.l_LeanTsTest_Vectors_uszCompl
const uszToNat = m.l_LeanTsTest_Vectors_uszToNat

const checks = [
  // getNumBits reports 32 under the 32-bit profile.
  ["nbits", nbits(), 32n],
  // UInt64 2^32 truncates to 0 in a 32-bit USize.
  ["uszOfU64(2^32)", uszToNat(uszOfU64(4294967296n)), 0n],
  // 2^32-1 survives (high bits already zero).
  ["uszOfU64(2^32-1)", uszToNat(uszOfU64(4294967295n)), 4294967295n],
  // USize add wraps at 2^32: (2^32-1) + 1 == 0.
  ["uszAddWrap", uszToNat(uszAdd(4294967295n, 1n)), 0n],
  // complement of 0 is the all-ones 32-bit word.
  ["uszCompl(0)", uszToNat(uszCompl(0n)), 4294967295n],
]

let ok = true
for (const [name, got, want] of checks) {
  const pass = got === want
  if (!pass) ok = false
  console.log(`usize32 ${show(name)} = ${show(got)} ${pass ? "PASS" : `FAIL (want ${show(want)})`}`)
}
if (!ok) {
  console.error("USIZE32 profile check FAILED")
  process.exit(1)
}
console.log("USIZE32 PASS: WORD_BITS=32 wraps at 2^32 and getNumBits=32")
