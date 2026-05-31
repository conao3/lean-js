// Deep mutual / cross-function tail-recursion: assert the trampolined cores
// run at N=1,000,000 without a JS stack overflow. The `lean --run` interpreter
// caps recursion far below this, so this lives node-side; the expected values
// are the closed forms (parity = N even/odd; cycle3 = N mod 3) that the same
// recursive Lean functions compute.
import { readFileSync } from 'node:fs';

const src = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');

// Structural check: the acyclic cross-function tail chain chainHead -> cs3 ->
// cs2 -> cs1 is a DAG of distinct size-1 SCCs with no self-edge, so the OLD
// SCC-only trampoline left every link as a stacking call. The uniform
// thunk-target mechanism must emit a `__tc` core for each tail-edge target.
// (cs0 and viaA/viaB are inlined away by the Lean compiler, so they have no
// surviving call site; the survivors are the four below.)
const wantCores = [
  'LeanJs_Demo_cs1__tc', 'LeanJs_Demo_cs2__tc',
  'LeanJs_Demo_cs3__tc', 'LeanJs_Demo_chainHead__tc',
];
let structOk = true;
for (const c of wantCores) {
  const has = src.includes(`function ${c}(`);
  if (!has) structOk = false;
  console.log(`core ${c} ${has ? 'PASS' : 'FAIL (no __tc core; acyclic link would stack)'}`);
}
if (!structOk) { console.error('acyclic-chain core check FAILED'); process.exit(1); }

const fn = new Function(src + `\nreturn { LeanJs_Demo_parityEven, LeanJs_Demo_parityOdd, LeanJs_Demo_cycle3, LeanJs_Demo_pingN, LeanJs_Demo_chainHead };`);
const { LeanJs_Demo_parityEven: parityEven, LeanJs_Demo_parityOdd: parityOdd, LeanJs_Demo_cycle3: cycle3, LeanJs_Demo_pingN: pingN, LeanJs_Demo_chainHead: chainHead } = fn();

const N = 1000000n;
const checks = [
  ['parityEven', Number(parityEven(N)), 1],          // 1,000,000 is even -> true (1)
  ['parityOdd', Number(parityOdd(N)), 0],            // even -> not odd -> false (0)
  ['cycle3', cycle3(N), 1n],                          // 1,000,000 mod 3 == 1
  ['chainHead', chainHead(N), N + 3n],               // acyclic 4-deep chain: n + 3
  // pingN self-loops N times; each step drives the cross-function tail edge
  // viaB -> viaA through the trampoline. acc starts 0, +1 per step -> N.
  ['pingN', pingN(N, 0n), N],
];

let ok = true;
for (const [name, got, want] of checks) {
  const pass = got === want;
  if (!pass) ok = false;
  console.log(`${name}(${N}) = ${got} ${pass ? 'PASS' : `FAIL (want ${want})`}`);
}
if (!ok) { console.error('TCO deep-recursion check FAILED'); process.exit(1); }
console.log('TCO-DEEP PASS: no stack overflow at N=1000000');
