import { readFileSync } from 'node:fs';

const src = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');
const exports = [
  'LeanJs_Fuzz_fNat', 'LeanJs_Fuzz_fInt', 'LeanJs_Fuzz_fU32', 'LeanJs_Fuzz_fU8',
  'LeanJs_Fuzz_fStr', 'LeanJs_Fuzz_fHash', 'LeanJs_Fuzz_fListNat', 'LeanJs_Fuzz_fArrNat',
];
const fn = new Function(src + `\nreturn { ${exports.join(', ')} };`);
const m = fn();

// List Nat: nil = scalar 0, cons = { tag:1, fields:[head, tail] } (head first).
const mkList = (arr) => arr.reduceRight((tl, h) => ({ tag: 1, fields: [h, tl] }), 0);
// Mirror LeanJs.Fuzz.unescape (replace order: \t, \n, then \\).
const unesc = (s) => s.replace(/\\t/g, '\t').replace(/\\n/g, '\n').replace(/\\\\/g, '\\');

const lines = readFileSync(0, 'utf8').split('\n').filter((l) => l.length > 0);
const out = [];
for (const line of lines) {
  const p = line.split('\t');
  switch (p[0]) {
    case 'NAT': out.push(`NAT\t${m.LeanJs_Fuzz_fNat(BigInt(p[1]))}`); break;
    case 'INT': out.push(`INT\t${m.LeanJs_Fuzz_fInt(BigInt(p[1]), BigInt(p[2]))}`); break;
    case 'U32': out.push(`U32\t${m.LeanJs_Fuzz_fU32(Number(p[1]) >>> 0, Number(p[2]) >>> 0)}`); break;
    case 'U8': out.push(`U8\t${m.LeanJs_Fuzz_fU8(Number(p[1]) & 255, Number(p[2]) & 255)}`); break;
    case 'STR': out.push(`STR\t${m.LeanJs_Fuzz_fStr(unesc(p[1] ?? ''))}`); break;
    case 'HASH': out.push(`HASH\t${m.LeanJs_Fuzz_fHash(unesc(p[1] ?? ''))}`); break;
    case 'LNAT': out.push(`LNAT\t${m.LeanJs_Fuzz_fListNat(mkList(p.slice(1).filter((x) => x).map(BigInt)))}`); break;
    case 'ANAT': out.push(`ANAT\t${m.LeanJs_Fuzz_fArrNat(p.slice(1).filter((x) => x).map(BigInt))}`); break;
    default: out.push(`ERR\t${line}`); break;
  }
}
process.stdout.write(out.join('\n') + (out.length ? '\n' : ''));
