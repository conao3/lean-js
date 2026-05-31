// Deterministic fuzz-input generator. A fixed edge-case block (seed-independent)
// is always emitted first, then `N` seeded-random vectors (mulberry32 keyed by
// SEED). One vector per line, TAB-separated: <tag>\t<field>... Strings escape
// TAB/newline/backslash so multibyte payloads survive the line transport.
const SEED = (process.argv[2] | 0) || 1;
const N = (process.argv[3] | 0) || 2000;

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const rnd = mulberry32(SEED);
const ri = (n) => Math.floor(rnd() * n);

const esc = (s) => s.replace(/\\/g, '\\\\').replace(/\t/g, '\\t').replace(/\n/g, '\\n');

const lines = [];
// --- fixed edge block (always emitted, seed-independent) ---
lines.push('NAT\t0', 'NAT\t1', 'NAT\t18446744073709551615', 'NAT\t18446744073709551616',
  'NAT\t123456789012345678901234567890');
lines.push('U32\t4294967295\t1', 'U32\t0\t0', 'U8\t0\t1', 'U8\t255\t255', 'U8\t200\t100');
lines.push('INT\t-1\t1', 'INT\t-7\t2', 'INT\t7\t-2', 'INT\t-7\t-2', 'INT\t9223372036854775808\t-1');
lines.push('STR\t', 'STR\ta', 'STR\t' + esc('é'), 'STR\t' + esc('世界'),
  'STR\t' + esc('\u{1F600}combiníng'), 'STR\t' + esc('a\tb'));
lines.push('HASH\t', 'HASH\ta', 'HASH\t' + esc('abcdefgh'), 'HASH\t' + esc('hello world'));
lines.push('LNAT\t', 'LNAT\t5', 'LNAT\t1\t2\t3\t4\t5');
lines.push('ANAT\t', 'ANAT\t9', 'ANAT\t10\t20\t30');

// random astral / combining / ascii code points for STR synthesis.
const randStr = () => {
  const k = ri(8);
  let s = '';
  for (let j = 0; j < k; j++) {
    const r = ri(4);
    if (r === 0) s += String.fromCodePoint(0x20 + ri(0x5f));        // ascii
    else if (r === 1) s += String.fromCodePoint(0x4e00 + ri(0x1000)); // CJK
    else if (r === 2) s += String.fromCodePoint(0x1F300 + ri(0x200)); // astral
    else s += String.fromCodePoint(0x300 + ri(0x40));               // combining
  }
  return s;
};

// --- seeded random block ---
for (let i = 0; i < N; i++) {
  const r = ri(7);
  if (r === 0) {
    lines.push(`NAT\t${ri(1e9)}${ri(1e9)}${ri(1e9)}`);
  } else if (r === 1) {
    const a = ri(4e9) - 2e9;
    let b = ri(200) - 100; if (b === 0) b = 1;
    lines.push(`INT\t${a}\t${b}`);
  } else if (r === 2) {
    lines.push(`U32\t${ri(4.5e9)}\t${ri(4.5e9)}`);
  } else if (r === 3) {
    lines.push(`U8\t${ri(300)}\t${ri(300)}`);
  } else if (r === 4) {
    const s = esc(randStr());
    lines.push(`STR\t${s}`);
    lines.push(`HASH\t${s}`);
  } else if (r === 5) {
    const k = ri(12); const els = [];
    for (let j = 0; j < k; j++) els.push(ri(100000));
    lines.push(['LNAT', ...els].join('\t'));
  } else {
    const k = ri(12); const els = [];
    for (let j = 0; j < k; j++) els.push(ri(100000));
    lines.push(['ANAT', ...els].join('\t'));
  }
}
process.stdout.write(lines.join('\n') + '\n');
