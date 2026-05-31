// Diff-test harness: load generated out.ts (plain JS) and run the same inputs
// as expected.lean, printing results in identical format.
import { readFileSync } from 'node:fs';

const src = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');
const exports = [
  'LeanJs_Demo_double', 'LeanJs_Demo_mkShifted', 'LeanJs_Demo_sumTo', 'LeanJs_Demo_fact',
  'LeanJs_Demo_mkMixed', 'LeanJs_Demo_mixedSum',
  'LeanJs_Demo_u32wrap', 'LeanJs_Demo_u8wrap',
  'LeanJs_Demo_intEdiv', 'LeanJs_Demo_intEmod', 'LeanJs_Demo_intNeg',
  'LeanJs_Demo_floatCalc',
  'LeanJs_Demo_strLen', 'LeanJs_Demo_strBytes', 'LeanJs_Demo_strGet0',
  'LeanJs_Demo_strGet1', 'LeanJs_Demo_strExtract',
  'LeanJs_Demo_arrSum', 'LeanJs_Demo_arrMapSum', 'LeanJs_Demo_arrRange',
  'LeanJs_Demo_arrGetD', 'LeanJs_Demo_arrAppend',
  'LeanJs_Demo_listSum', 'LeanJs_Demo_listLen', 'LeanJs_Demo_listRev',
  'LeanJs_Demo_listMapSum',
  'LeanTodo_TodoList_add', 'LeanTodo_TodoList_toggle',
  'LeanTodo_TodoList_remove', 'LeanTodo_TodoList_step',
];
const fn = new Function(src + `\nreturn { ${exports.join(', ')} };`);
const m = fn();
const {
  LeanJs_Demo_double: double,
  LeanJs_Demo_mkShifted: mkShifted,
  LeanJs_Demo_sumTo: sumTo,
  LeanJs_Demo_fact: fact,
  LeanJs_Demo_mkMixed: mkMixed,
  LeanJs_Demo_mixedSum: mixedSum,
  LeanJs_Demo_u32wrap: u32wrap,
  LeanJs_Demo_u8wrap: u8wrap,
  LeanJs_Demo_intEdiv: intEdiv,
  LeanJs_Demo_intEmod: intEmod,
  LeanJs_Demo_intNeg: intNeg,
  LeanJs_Demo_floatCalc: floatCalc,
  LeanJs_Demo_strLen: strLen,
  LeanJs_Demo_strBytes: strBytes,
  LeanJs_Demo_strGet0: strGet0,
  LeanJs_Demo_strGet1: strGet1,
  LeanJs_Demo_strExtract: strExtract,
  LeanJs_Demo_arrSum: arrSum,
  LeanJs_Demo_arrMapSum: arrMapSum,
  LeanJs_Demo_arrRange: arrRange,
  LeanJs_Demo_arrGetD: arrGetD,
  LeanJs_Demo_arrAppend: arrAppend,
  LeanJs_Demo_listSum: listSum,
  LeanJs_Demo_listLen: listLen,
  LeanJs_Demo_listRev: listRev,
  LeanJs_Demo_listMapSum: listMapSum,
  LeanTodo_TodoList_add: add,
  LeanTodo_TodoList_toggle: toggle,
  LeanTodo_TodoList_remove: remove,
  LeanTodo_TodoList_step: step,
} = m;

// Lean's Float.toString uses C `%f` (fixed 6 decimal places).
const leanFloatToString = (x) => x.toFixed(6);

// Point = { tag:0, fields:[x,y] }
const P = (x, y) => ({ tag: 0, fields: [x, y] });
const showP = (p) => `(${p.fields[0]},${p.fields[1]})`;

console.log(`double 0 = ${double(0n)}`);
console.log(`double 7 = ${double(7n)}`);
console.log(`double 1000000 = ${double(1000000n)}`);
console.log(`mkShifted(3,4) = ${showP(mkShifted(P(3n, 4n)))}`);
console.log(`mkShifted(0,0) = ${showP(mkShifted(P(0n, 0n)))}`);
console.log(`mkShifted(10,100) = ${showP(mkShifted(P(10n, 100n)))}`);
console.log(`sumTo 0 = ${sumTo(0n)}`);
console.log(`sumTo 5 = ${sumTo(5n)}`);
console.log(`sumTo 100 = ${sumTo(100n)}`);
console.log(`sumTo 100000 = ${sumTo(100000n)}`);
console.log(`fact 0 = ${fact(0n)}`);
console.log(`fact 5 = ${fact(5n)}`);
console.log(`fact 10 = ${fact(10n)}`);

// ---- Mixed ctor (object + packed sub-word scalars) ----
// Lean's layout pass packs region S as: d:UInt16 @0, b:UInt8 @2, c:UInt8 @3
// (alignment-driven). Reading those byte offsets returns the fields distinctly,
// where a single fields[] keyed by word-slot index would have collided them.
const mx = mkMixed(100n, 7, 9, 1000);
console.log(`mixed b = ${mx.sdata.getUint8(2)}`);
console.log(`mixed c = ${mx.sdata.getUint8(3)}`);
console.log(`mixed d = ${mx.sdata.getUint16(0, true)}`);
console.log(`mixedSum = ${mixedSum(mx)}`);
const m2 = mkMixed(0n, 255, 1, 65535);
console.log(`mixed2 b = ${m2.sdata.getUint8(2)}`);
console.log(`mixed2 c = ${m2.sdata.getUint8(3)}`);
console.log(`mixed2 d = ${m2.sdata.getUint16(0, true)}`);
console.log(`mixedSum2 = ${mixedSum(m2)}`);

// ---- Numeric tower: UInt wrap, Int Euclidean div/mod, Float ----
console.log(`u32wrap = ${u32wrap(4000000000, 1000000000)}`);
console.log(`u8wrap = ${u8wrap(3, 10)}`);
console.log(`intEdiv = ${intEdiv(-12n, 7n)}`);
console.log(`intEmod = ${intEmod(-12n, 7n)}`);
console.log(`intEdiv2 = ${intEdiv(12n, -7n)}`);
console.log(`intEmod2 = ${intEmod(12n, -7n)}`);
console.log(`intNeg = ${intNeg(42n)}`);
console.log(`floatCalc = ${leanFloatToString(floatCalc(3.0, 4.0))}`);

// ---- String UTF-8 byte semantics over a multibyte (Japanese) string ----
const jp = 'あいう'; // each char is 3 UTF-8 bytes; length=3 code points, 9 bytes
console.log(`strLen = ${strLen(jp)}`);
console.log(`strBytes = ${strBytes(jp)}`);
console.log(`strGet0 = ${String.fromCodePoint(strGet0(jp))}`);
console.log(`strGet1 = ${String.fromCodePoint(strGet1(jp))}`);
console.log(`strExtract03 = ${strExtract(jp, 0n, 3n)}`);
console.log(`strExtract39 = ${strExtract(jp, 3n, 9n)}`);

// ---- Array / List operations ----
// Lean prints Array as `#[a, b, ...]`, List as `[a, b, ...]`.
const showArr = (a) => `#[${a.join(', ')}]`;
const listToArr2 = (l) => {
  const out = [];
  let cur = l;
  while (typeof cur !== 'number' && cur.tag === 1) { out.push(cur.fields[0]); cur = cur.fields[1]; }
  return out;
};
const showLst = (l) => `[${listToArr2(l).join(', ')}]`;
// List literal: nil = 0, cons = {tag:1, fields:[head, tail]}
const lst2list = (arr) => arr.reduceRight((tl, h) => ({ tag: 1, fields: [h, tl] }), 0);
const arr = [1n, 2n, 3n, 4n, 5n];
console.log(`arrSum = ${arrSum(arr)}`);
console.log(`arrMapSum = ${arrMapSum(arr)}`);
console.log(`arrRange = ${showArr(arrRange(5n))}`);
console.log(`arrGetD2 = ${arrGetD(arr, 2n)}`);
console.log(`arrGetD9 = ${arrGetD(arr, 9n)}`);
console.log(`arrAppend = ${showArr(arrAppend(arr, [6n, 7n]))}`);
const lst = lst2list([10n, 20n, 30n]);
console.log(`listSum = ${listSum(lst)}`);
console.log(`listLen = ${listLen(lst)}`);
console.log(`listRev = ${showLst(listRev(lst))}`);
console.log(`listMapSum = ${listMapSum(lst)}`);

// ---- TodoList JS model ----
// List: nil = 0, cons = { tag:1, fields:[head, tail] }
// Todo: { tag:0, fields:[id, title, done] }   (done is scalar 0/1)
// TodoList: { tag:0, fields:[items, nextId] }
// Command: add(title)=tag0, toggle(id)=tag1, remove(id)=tag2
const empty = { tag: 0, fields: [0, 0n] };
const Cadd = (title) => ({ tag: 0, fields: [title] });
const Ctoggle = (id) => ({ tag: 1, fields: [id] });
const Cremove = (id) => ({ tag: 2, fields: [id] });

const listToArr = (l) => {
  const out = [];
  let cur = l;
  while (typeof cur !== 'number' && cur.tag === 1) {
    out.push(cur.fields[0]);
    cur = cur.fields[1];
  }
  return out;
};
// Todo: { tag:0, fields:[id, title], sdata:[done:u8 @0] } — done is a packed
// scalar in region S, read via the byte-addressed DataView (sproj layout).
const showTodo = (t) => `${t.fields[0]}:${t.fields[1]}:${t.sdata.getUint8(0) ? 'x' : ' '}`;
const showList = (l) =>
  '[' + listToArr(l.fields[0]).map(showTodo).join(',') + ']@' + l.fields[1];

const l1 = add(empty, 'buy milk');
console.log(`add1 = ${showList(l1)}`);
const l2 = add(l1, 'walk dog');
console.log(`add2 = ${showList(l2)}`);
const l3 = add(l2, 'write code');
console.log(`add3 = ${showList(l3)}`);
const l4 = toggle(l3, 1n);
console.log(`toggle1 = ${showList(l4)}`);
const l5 = toggle(l4, 0n);
console.log(`toggle0 = ${showList(l5)}`);
const l6 = remove(l5, 1n);
console.log(`remove1 = ${showList(l6)}`);
const l7 = step(l6, Cadd('new task'));
console.log(`step-add = ${showList(l7)}`);
const l8 = step(l7, Ctoggle(2n));
console.log(`step-toggle = ${showList(l8)}`);
const l9 = step(l8, Cremove(0n));
console.log(`step-remove = ${showList(l9)}`);
