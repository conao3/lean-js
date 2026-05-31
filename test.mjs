// Diff-test harness: imports generated out.ts (as a module via dynamic eval),
// runs the same 3 inputs as expected.lean, prints results in identical format.
import { readFileSync } from 'node:fs';

const src = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');
// out.ts is plain JS (no TS types in the emitted code); eval into this scope.
const mod = {};
const fn = new Function(src + '\nreturn { double, mkShifted };');
const { double, mkShifted } = fn();

// double
console.log(`double 0 = ${double(0n)}`);
console.log(`double 7 = ${double(7n)}`);
console.log(`double 1000000 = ${double(1000000n)}`);

// mkShifted: Point = { tag:0, fields:[x, y] }
const P = (x, y) => ({ tag: 0, fields: [x, y] });
const show = (p) => `(${p.fields[0]},${p.fields[1]})`;
console.log(`mkShifted(3,4) = ${show(mkShifted(P(3n, 4n)))}`);
console.log(`mkShifted(0,0) = ${show(mkShifted(P(0n, 0n)))}`);
console.log(`mkShifted(10,100) = ${show(mkShifted(P(10n, 100n)))}`);
