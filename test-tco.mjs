// Deep mutual / cross-function tail-recursion: assert the trampolined cores
// run at N=1,000,000 without a JS stack overflow. The `lean --run` interpreter
// caps recursion far below this, so this lives node-side; the expected values
// are the closed forms (parity = N even/odd; cycle3 = N mod 3) that the same
// recursive Lean functions compute.
import { readFileSync } from 'node:fs';

const src = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');
const fn = new Function(src + `\nreturn { LeanJs_Demo_parityEven, LeanJs_Demo_parityOdd, LeanJs_Demo_cycle3 };`);
const { LeanJs_Demo_parityEven: parityEven, LeanJs_Demo_parityOdd: parityOdd, LeanJs_Demo_cycle3: cycle3 } = fn();

const N = 1000000n;
const checks = [
  ['parityEven', Number(parityEven(N)), 1],          // 1,000,000 is even -> true (1)
  ['parityOdd', Number(parityOdd(N)), 0],            // even -> not odd -> false (0)
  ['cycle3', cycle3(N), 1n],                          // 1,000,000 mod 3 == 1
];

let ok = true;
for (const [name, got, want] of checks) {
  const pass = got === want;
  if (!pass) ok = false;
  console.log(`${name}(${N}) = ${got} ${pass ? 'PASS' : `FAIL (want ${want})`}`);
}
if (!ok) { console.error('TCO deep-recursion check FAILED'); process.exit(1); }
console.log('TCO-DEEP PASS: no stack overflow at N=1000000');
