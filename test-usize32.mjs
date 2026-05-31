// 32-bit USize profile: WORD_BITS is the single knob that routes the usize
// arithmetic width, System.Platform.getNumBits, the UInt64->USize truncation,
// and the packed-usize ctor slot size. Flip it to 32 in the generated source and
// assert that USize wraps at 2^32 and getNumBits reports 32. Real `lean` on this
// 64-bit host cannot serve as the oracle for a 32-bit target (cross-compilation
// is out of scope), so the 32-bit profile is checked against hand-computed
// literals; the 64-bit profile is the one the native oracle (oracle-fns) covers.
import { readFileSync } from 'node:fs';

const src64 = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');
if (!src64.includes('const WORD_BITS = 64;')) {
  console.error('USIZE32 FAIL: WORD_BITS knob not found in prelude');
  process.exit(1);
}
const src32 = src64.replace('const WORD_BITS = 64;', 'const WORD_BITS = 32;');

const load = (src) => {
  const fn = new Function(src + `\nreturn { LeanJs_Demo_nbits, LeanJs_Demo_uszOfU64, LeanJs_Demo_uszAdd, LeanJs_Demo_uszCompl, LeanJs_Demo_uszToNat };`);
  return fn();
};

const m = load(src32);
const nbits = m.LeanJs_Demo_nbits;
const uszOfU64 = m.LeanJs_Demo_uszOfU64;
const uszAdd = m.LeanJs_Demo_uszAdd;
const uszCompl = m.LeanJs_Demo_uszCompl;
const uszToNat = m.LeanJs_Demo_uszToNat;

const checks = [
  // getNumBits reports 32 under the 32-bit profile.
  ['nbits', nbits(), 32n],
  // UInt64 2^32 truncates to 0 in a 32-bit USize.
  ['uszOfU64(2^32)', uszToNat(uszOfU64(4294967296n)), 0n],
  // 2^32-1 survives (high bits already zero).
  ['uszOfU64(2^32-1)', uszToNat(uszOfU64(4294967295n)), 4294967295n],
  // USize add wraps at 2^32: (2^32-1) + 1 == 0.
  ['uszAddWrap', uszToNat(uszAdd(4294967295n, 1n)), 0n],
  // complement of 0 is the all-ones 32-bit word.
  ['uszCompl(0)', uszToNat(uszCompl(0n)), 4294967295n],
];

let ok = true;
for (const [name, got, want] of checks) {
  const pass = got === want;
  if (!pass) ok = false;
  console.log(`usize32 ${name} = ${got} ${pass ? 'PASS' : `FAIL (want ${want})`}`);
}
if (!ok) { console.error('USIZE32 profile check FAILED'); process.exit(1); }
console.log('USIZE32 PASS: WORD_BITS=32 wraps at 2^32 and getNumBits=32');
