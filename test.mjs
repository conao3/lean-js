// Diff-test harness: load generated out.ts (plain JS) and run the same inputs
// as expected.lean, printing results in identical format.
import { readFileSync } from 'node:fs';

const src = readFileSync(new URL('./out.ts', import.meta.url), 'utf8');
const exports = [
  'LeanTsTest_Vectors_double', 'LeanTsTest_Vectors_mkShifted', 'LeanTsTest_Vectors_sumTo', 'LeanTsTest_Vectors_fact',
  'LeanTsTest_Vectors_mkMixed', 'LeanTsTest_Vectors_mixedSum',
  'LeanTsTest_Vectors_u32wrap', 'LeanTsTest_Vectors_u8wrap',
  'LeanTsTest_Vectors_intEdiv', 'LeanTsTest_Vectors_intEmod', 'LeanTsTest_Vectors_intNeg',
  'LeanTsTest_Vectors_floatCalc',
  'LeanTsTest_Vectors_strLen', 'LeanTsTest_Vectors_strBytes', 'LeanTsTest_Vectors_strGet0',
  'LeanTsTest_Vectors_strGet1', 'LeanTsTest_Vectors_strExtract',
  'LeanTsTest_Vectors_arrSum', 'LeanTsTest_Vectors_arrMapSum', 'LeanTsTest_Vectors_arrRange',
  'LeanTsTest_Vectors_arrGetD', 'LeanTsTest_Vectors_arrAppend',
  'LeanTsTest_Vectors_listSum', 'LeanTsTest_Vectors_listLen', 'LeanTsTest_Vectors_listRev',
  'LeanTsTest_Vectors_listMapSum',
  'LeanTsTest_Vectors_parityEven', 'LeanTsTest_Vectors_parityOdd', 'LeanTsTest_Vectors_cycle3',
  'LeanTsTest_Vectors_i8wrap', 'LeanTsTest_Vectors_i8neg', 'LeanTsTest_Vectors_i8div', 'LeanTsTest_Vectors_i8mod',
  'LeanTsTest_Vectors_i8shr', 'LeanTsTest_Vectors_i16wrap', 'LeanTsTest_Vectors_i32wrap', 'LeanTsTest_Vectors_i64mul',
  'LeanTsTest_Vectors_i8toInt', 'LeanTsTest_Vectors_i32toInt',
  'LeanTsTest_Vectors_floatStr', 'LeanTsTest_Vectors_float32Str',
  'LeanTsTest_Vectors_mkSPack', 'LeanTsTest_Vectors_spackA', 'LeanTsTest_Vectors_spackB',
  'LeanTsTest_Vectors_spackC', 'LeanTsTest_Vectors_spackE', 'LeanTsTest_Vectors_spackF',
  'LeanTsTest_Vectors_spackG', 'LeanTsTest_Vectors_spackSum',
  'lean_int8_to_int', 'lean_int16_to_int', 'lean_int32_to_int', 'lean_int64_to_int_sint',
  'LeanTsTest_Vectors_chainHead', 'LeanTsTest_Vectors_pingN',
  'LeanTsTest_Vectors_ftan', 'LeanTsTest_Vectors_fasin', 'LeanTsTest_Vectors_facos', 'LeanTsTest_Vectors_fatan',
  'LeanTsTest_Vectors_fatan2', 'LeanTsTest_Vectors_fsinh', 'LeanTsTest_Vectors_fcosh', 'LeanTsTest_Vectors_ftanh',
  'LeanTsTest_Vectors_fexp2', 'LeanTsTest_Vectors_flog2', 'LeanTsTest_Vectors_flog10', 'LeanTsTest_Vectors_fcbrt',
  'LeanTsTest_Vectors_ftoBits', 'LeanTsTest_Vectors_fofBits', 'LeanTsTest_Vectors_ffrExpM', 'LeanTsTest_Vectors_ffrExpE',
  'LeanTsTest_Vectors_f32tan', 'LeanTsTest_Vectors_f32exp', 'LeanTsTest_Vectors_f32log', 'LeanTsTest_Vectors_f32cbrt',
  'LeanTsTest_Vectors_f32toBits',
  'LeanTsTest_Vectors_nbits', 'LeanTsTest_Vectors_uszOfU64', 'LeanTsTest_Vectors_uszAdd',
  'LeanTsTest_Vectors_uszCompl', 'LeanTsTest_Vectors_uszToNat',
  'LeanTsTest_HigherOrder_hofApply', 'LeanTsTest_HigherOrder_listMapLam', 'LeanTsTest_HigherOrder_listFilterLam',
  'LeanTsTest_HigherOrder_listFoldlLam', 'LeanTsTest_HigherOrder_arrMapLam', 'LeanTsTest_HigherOrder_applyAdders',
  'LeanTsTest_HigherOrder_currySplit', 'LeanTsTest_HigherOrder_optSeq', 'LeanTsTest_HigherOrder_exSeq',
  'LeanTsTest_HigherOrder_fmapList', 'LeanTsTest_HigherOrder_safeDivStr', 'LeanTsTest_HigherOrder_hmDemo',
  'LeanTsTest_HigherOrder_cpsCount', 'LeanTsTest_HigherOrder_cpsSum',
  'LeanTsTest_Vectors_TodoList_add', 'LeanTsTest_Vectors_TodoList_toggle',
  'LeanTsTest_Vectors_TodoList_remove', 'LeanTsTest_Vectors_TodoList_step',
];
const fn = new Function(src + `\nreturn { ${exports.join(', ')} };`);
const m = fn();
const {
  LeanTsTest_Vectors_double: double,
  LeanTsTest_Vectors_mkShifted: mkShifted,
  LeanTsTest_Vectors_sumTo: sumTo,
  LeanTsTest_Vectors_fact: fact,
  LeanTsTest_Vectors_mkMixed: mkMixed,
  LeanTsTest_Vectors_mixedSum: mixedSum,
  LeanTsTest_Vectors_u32wrap: u32wrap,
  LeanTsTest_Vectors_u8wrap: u8wrap,
  LeanTsTest_Vectors_intEdiv: intEdiv,
  LeanTsTest_Vectors_intEmod: intEmod,
  LeanTsTest_Vectors_intNeg: intNeg,
  LeanTsTest_Vectors_floatCalc: floatCalc,
  LeanTsTest_Vectors_strLen: strLen,
  LeanTsTest_Vectors_strBytes: strBytes,
  LeanTsTest_Vectors_strGet0: strGet0,
  LeanTsTest_Vectors_strGet1: strGet1,
  LeanTsTest_Vectors_strExtract: strExtract,
  LeanTsTest_Vectors_arrSum: arrSum,
  LeanTsTest_Vectors_arrMapSum: arrMapSum,
  LeanTsTest_Vectors_arrRange: arrRange,
  LeanTsTest_Vectors_arrGetD: arrGetD,
  LeanTsTest_Vectors_arrAppend: arrAppend,
  LeanTsTest_Vectors_listSum: listSum,
  LeanTsTest_Vectors_listLen: listLen,
  LeanTsTest_Vectors_listRev: listRev,
  LeanTsTest_Vectors_listMapSum: listMapSum,
  LeanTsTest_Vectors_parityEven: parityEven,
  LeanTsTest_Vectors_parityOdd: parityOdd,
  LeanTsTest_Vectors_cycle3: cycle3,
  LeanTsTest_Vectors_i8wrap: i8wrap,
  LeanTsTest_Vectors_i8neg: i8neg,
  LeanTsTest_Vectors_i8div: i8div,
  LeanTsTest_Vectors_i8mod: i8mod,
  LeanTsTest_Vectors_i8shr: i8shr,
  LeanTsTest_Vectors_i16wrap: i16wrap,
  LeanTsTest_Vectors_i32wrap: i32wrap,
  LeanTsTest_Vectors_i64mul: i64mul,
  LeanTsTest_Vectors_i8toInt: i8toInt,
  LeanTsTest_Vectors_i32toInt: i32toInt,
  LeanTsTest_Vectors_floatStr: floatStr,
  LeanTsTest_Vectors_float32Str: float32Str,
  LeanTsTest_Vectors_mkSPack: mkSPack,
  LeanTsTest_Vectors_spackA: spackA,
  LeanTsTest_Vectors_spackB: spackB,
  LeanTsTest_Vectors_spackC: spackC,
  LeanTsTest_Vectors_spackE: spackE,
  LeanTsTest_Vectors_spackF: spackF,
  LeanTsTest_Vectors_spackG: spackG,
  LeanTsTest_Vectors_spackSum: spackSum,
  lean_int8_to_int: i8ToInt,
  lean_int16_to_int: i16ToInt,
  lean_int32_to_int: i32ToInt,
  lean_int64_to_int_sint: i64ToInt,
  LeanTsTest_Vectors_chainHead: chainHead,
  LeanTsTest_Vectors_pingN: pingN,
  LeanTsTest_Vectors_ftan: ftan,
  LeanTsTest_Vectors_fasin: fasin,
  LeanTsTest_Vectors_facos: facos,
  LeanTsTest_Vectors_fatan: fatan,
  LeanTsTest_Vectors_fatan2: fatan2,
  LeanTsTest_Vectors_fsinh: fsinh,
  LeanTsTest_Vectors_fcosh: fcosh,
  LeanTsTest_Vectors_ftanh: ftanh,
  LeanTsTest_Vectors_fexp2: fexp2,
  LeanTsTest_Vectors_flog2: flog2,
  LeanTsTest_Vectors_flog10: flog10,
  LeanTsTest_Vectors_fcbrt: fcbrt,
  LeanTsTest_Vectors_ftoBits: ftoBits,
  LeanTsTest_Vectors_fofBits: fofBits,
  LeanTsTest_Vectors_ffrExpM: ffrExpM,
  LeanTsTest_Vectors_ffrExpE: ffrExpE,
  LeanTsTest_Vectors_f32tan: f32tan,
  LeanTsTest_Vectors_f32exp: f32exp,
  LeanTsTest_Vectors_f32log: f32log,
  LeanTsTest_Vectors_f32cbrt: f32cbrt,
  LeanTsTest_Vectors_f32toBits: f32toBits,
  LeanTsTest_Vectors_nbits: nbits,
  LeanTsTest_Vectors_uszOfU64: uszOfU64,
  LeanTsTest_Vectors_uszAdd: uszAdd,
  LeanTsTest_Vectors_uszCompl: uszCompl,
  LeanTsTest_Vectors_uszToNat: uszToNat,
  LeanTsTest_HigherOrder_hofApply: hofApply,
  LeanTsTest_HigherOrder_listMapLam: listMapLam,
  LeanTsTest_HigherOrder_listFilterLam: listFilterLam,
  LeanTsTest_HigherOrder_listFoldlLam: listFoldlLam,
  LeanTsTest_HigherOrder_arrMapLam: arrMapLam,
  LeanTsTest_HigherOrder_applyAdders: applyAdders,
  LeanTsTest_HigherOrder_currySplit: currySplit,
  LeanTsTest_HigherOrder_optSeq: optSeq,
  LeanTsTest_HigherOrder_exSeq: exSeq,
  LeanTsTest_HigherOrder_fmapList: fmapList,
  LeanTsTest_HigherOrder_safeDivStr: safeDivStr,
  LeanTsTest_HigherOrder_hmDemo: hmDemo,
  LeanTsTest_HigherOrder_cpsCount: cpsCount,
  LeanTsTest_HigherOrder_cpsSum: cpsSum,
  LeanTsTest_Vectors_TodoList_add: add,
  LeanTsTest_Vectors_TodoList_toggle: toggle,
  LeanTsTest_Vectors_TodoList_remove: remove,
  LeanTsTest_Vectors_TodoList_step: step,
} = m;

// Lean's Float.toString uses C `%f` (6 decimals); route through the generated
// floatStr so the harness exercises the real prelude renderer (NaN/Inf/-0.0).
const leanFloatToString = (x) => floatStr(x);

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

// ---- Mutual / cross-function TCO (Bool prints as true/false; scalar 0/1) ----
const showBool = (b) => (b ? 'true' : 'false');
console.log(`parityEven 7 = ${showBool(parityEven(7n))}`);
console.log(`parityOdd 7 = ${showBool(parityOdd(7n))}`);
console.log(`parityEven 3000 = ${showBool(parityEven(3000n))}`);
console.log(`parityOdd 3000 = ${showBool(parityOdd(3000n))}`);
console.log(`cycle3 0 = ${cycle3(0n)}`);
console.log(`cycle3 1 = ${cycle3(1n)}`);
console.log(`cycle3 2 = ${cycle3(2n)}`);
console.log(`cycle3 3000 = ${cycle3(3000n)}`);

// ---- Signed fixed-width ints (bigint repr; values equal their .toInt) ----
console.log(`i8wrap = ${i8wrap(127n, 1n)}`);
console.log(`i8neg = ${i8neg(-128n)}`);
console.log(`i8div = ${i8div(-128n, -1n)}`);
console.log(`i8div0 = ${i8div(5n, 0n)}`);
console.log(`i8mod = ${i8mod(-7n, 2n)}`);
console.log(`i8mod2 = ${i8mod(7n, -2n)}`);
console.log(`i8shr = ${i8shr(-8n, 1n)}`);
console.log(`i16wrap = ${i16wrap(256n, 256n)}`);
console.log(`i32wrap = ${i32wrap(2147483647n, 1n)}`);
console.log(`i64mul = ${i64mul(4294967296n, 4294967296n)}`);
console.log(`i8toInt = ${i8toInt(-5n)}`);
console.log(`i32toInt = ${i32toInt(-100n)}`);

// ---- Float / Float32 toString edge cases ----
console.log(`fstr0 = ${floatStr(0.0)}`);
console.log(`fstrPi = ${floatStr(3.14)}`);
console.log(`fstrNeg0 = ${floatStr(-0.0)}`);
console.log(`fstrInf = ${floatStr(1.0 / 0.0)}`);
console.log(`fstrNInf = ${floatStr(-1.0 / 0.0)}`);
console.log(`fstrNaN = ${floatStr(0.0 / 0.0)}`);
console.log(`fstrBig = ${floatStr(123456789.123456789)}`);
console.log(`fstr1e20 = ${floatStr(1e20)}`);
console.log(`fstr1e21 = ${floatStr(1e21)}`);
console.log(`fstrNeg = ${floatStr(-2.5)}`);
console.log(`f32str = ${float32Str(16777217.0)}`);
console.log(`f32strPi = ${float32Str(3.14)}`);

// ---- Packed signed-scalar fields (Int8/16/32/64) + Float/Float32 in region S ----
// Stored via the unsigned/float DataView setters (no signed IRType at 4.35.0);
// the signed value is recovered at the toInt boundary (lean_int*_to_int), which
// is exactly how Lean's compiled code reinterprets the raw uintN bytes. Floats
// are exact. spackSum returns Int, so it reinterprets all four signed fields.
const sp = mkSPack(100n, -5n, -300n, -70000n, -5000000000n, -2.5, 1.5);
console.log(`spackA = ${i8ToInt(spackA(sp))}`);
console.log(`spackB = ${i16ToInt(spackB(sp))}`);
console.log(`spackC = ${i32ToInt(spackC(sp))}`);
console.log(`spackE = ${i64ToInt(spackE(sp))}`);
console.log(`spackF = ${floatStr(spackF(sp))}`);
console.log(`spackG = ${float32Str(spackG(sp))}`);
console.log(`spackSum = ${spackSum(sp)}`);

// ---- Higher-order / closure / typeclass / exception (DemoHO) ----
// Option Nat: none = 0, some x = { tag:1, fields:[x] }. Lean prints
// `none`/`some x`. Except ε α: error = tag 0, ok = tag 1; Lean prints
// `Except.error e`/`Except.ok v` via its Repr.
const showOpt = (o) => (typeof o === 'number' ? 'none' : `(some ${o.fields[0]})`);
const showExc = (e) => (e.tag === 1 ? `ok: ${e.fields[0]}` : `error: ${e.fields[0]}`);
console.log(`hofApply = ${hofApply()}`);
console.log(`listMapLam = ${showLst(listMapLam(lst2list([1n, 2n, 3n])))}`);
console.log(`listFilterLam = ${showLst(listFilterLam(lst2list([1n, 2n, 3n, 4n])))}`);
console.log(`listFoldlLam = ${listFoldlLam(lst2list([1n, 2n, 3n]))}`);
console.log(`arrMapLam = ${showArr(arrMapLam([1n, 2n, 3n]))}`);
console.log(`applyAdders = ${applyAdders(5n)}`);
console.log(`currySplit = ${currySplit(1n)}`);
console.log(`optSeq = ${showOpt(optSeq())}`);
console.log(`exSeq = ${showExc(exSeq())}`);
console.log(`fmapList = ${showLst(fmapList(lst2list([1n, 2n, 3n])))}`);
console.log(`safeDiv 10 2 = ${safeDivStr(10n, 2n)}`);
console.log(`safeDiv 10 0 = ${safeDivStr(10n, 0n)}`);
console.log(`hmDemo = ${hmDemo()}`);
console.log(`cpsCount = ${cpsCount(10000n)}`);
console.log(`cpsSum = ${cpsSum(50000n)}`);
console.log(`chainHead 10 = ${chainHead(10n)}`);
console.log(`pingN 5 0 = ${pingN(5n, 0n)}`);
console.log(`ftan = ${floatStr(ftan(1.0))}`);
console.log(`fasin = ${floatStr(fasin(0.5))}`);
console.log(`facos = ${floatStr(facos(0.5))}`);
console.log(`fatan = ${floatStr(fatan(2.0))}`);
console.log(`fatan2 = ${floatStr(fatan2(1.0, 2.0))}`);
console.log(`fsinh = ${floatStr(fsinh(1.0))}`);
console.log(`fcosh = ${floatStr(fcosh(1.0))}`);
console.log(`ftanh = ${floatStr(ftanh(1.0))}`);
console.log(`fexp2 = ${floatStr(fexp2(10.0))}`);
console.log(`flog2 = ${floatStr(flog2(1024.0))}`);
console.log(`flog10 = ${floatStr(flog10(1000.0))}`);
console.log(`fcbrt = ${floatStr(fcbrt(27.0))}`);
console.log(`ftoBits = ${ftoBits(1.0)}`);
console.log(`fofBits = ${floatStr(fofBits(4607182418800017408n))}`);
console.log(`ffrExpM = ${floatStr(ffrExpM(12.0))}`);
console.log(`ffrExpE = ${ffrExpE(12.0)}`);
console.log(`f32tan = ${float32Str(f32tan(1.0))}`);
console.log(`f32exp = ${float32Str(f32exp(2.0))}`);
console.log(`f32log = ${float32Str(f32log(10.0))}`);
console.log(`f32cbrt = ${float32Str(f32cbrt(27.0))}`);
console.log(`f32toBits = ${f32toBits(1.0)}`);
console.log(`nbits = ${nbits()}`);
console.log(`uszOfU64 = ${uszToNat(uszOfU64(4294967296n))}`);
console.log(`uszAddWrap = ${uszToNat(uszAdd(0xFFFFFFFFFFFFFFFFn, 1n))}`);
console.log(`uszCompl = ${uszToNat(uszCompl(0n))}`);

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
