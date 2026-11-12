// Diff-test harness: import the generated modules and run the same inputs as
// LeanTsTest/VectorsMain.lean, printing results in identical format.
import * as L from "../../src/runtime/index.ts"
import * as vectors from "../../test-out/vectors.ts"
import * as higherOrder from "../../test-out/higher-order.ts"

const show = (x) => String(x)

const m = { ...L, ...vectors, ...higherOrder }
const {
  l_LeanTsTest_Vectors_double: double,
  l_LeanTsTest_Vectors_mkShifted: mkShifted,
  l_LeanTsTest_Vectors_sumTo: sumTo,
  l_LeanTsTest_Vectors_fact: fact,
  l_LeanTsTest_Vectors_mkMixed: mkMixed,
  l_LeanTsTest_Vectors_mixedSum: mixedSum,
  l_LeanTsTest_Vectors_u32wrap: u32wrap,
  l_LeanTsTest_Vectors_u8wrap: u8wrap,
  l_LeanTsTest_Vectors_intEdiv: intEdiv,
  l_LeanTsTest_Vectors_intEmod: intEmod,
  l_LeanTsTest_Vectors_intNeg: intNeg,
  l_LeanTsTest_Vectors_floatCalc: floatCalc,
  l_LeanTsTest_Vectors_strLen: strLen,
  l_LeanTsTest_Vectors_strBytes: strBytes,
  l_LeanTsTest_Vectors_strGet0: strGet0,
  l_LeanTsTest_Vectors_strGet1: strGet1,
  l_LeanTsTest_Vectors_strExtract: strExtract,
  l_LeanTsTest_Vectors_strLt: strLt,
  l_LeanTsTest_Vectors_arrSum: arrSum,
  l_LeanTsTest_Vectors_arrMapSum: arrMapSum,
  l_LeanTsTest_Vectors_arrRange: arrRange,
  l_LeanTsTest_Vectors_arrGetD: arrGetD,
  l_LeanTsTest_Vectors_arrAppend: arrAppend,
  l_LeanTsTest_Vectors_listSum: listSum,
  l_LeanTsTest_Vectors_listLen: listLen,
  l_LeanTsTest_Vectors_listRev: listRev,
  l_LeanTsTest_Vectors_listMapSum: listMapSum,
  l_LeanTsTest_Vectors_parityEven: parityEven,
  l_LeanTsTest_Vectors_parityOdd: parityOdd,
  l_LeanTsTest_Vectors_cycle3: cycle3,
  l_LeanTsTest_Vectors_i8wrap: i8wrap,
  l_LeanTsTest_Vectors_i8neg: i8neg,
  l_LeanTsTest_Vectors_i8div: i8div,
  l_LeanTsTest_Vectors_i8mod: i8mod,
  l_LeanTsTest_Vectors_i8shr: i8shr,
  l_LeanTsTest_Vectors_i16wrap: i16wrap,
  l_LeanTsTest_Vectors_i32wrap: i32wrap,
  l_LeanTsTest_Vectors_i64mul: i64mul,
  l_LeanTsTest_Vectors_i8toInt: i8toInt,
  l_LeanTsTest_Vectors_i32toInt: i32toInt,
  l_LeanTsTest_Vectors_floatStr: floatStr,
  l_LeanTsTest_Vectors_float32Str: float32Str,
  l_LeanTsTest_Vectors_mkSPack: mkSPack,
  l_LeanTsTest_Vectors_spackA: spackA,
  l_LeanTsTest_Vectors_spackB: spackB,
  l_LeanTsTest_Vectors_spackC: spackC,
  l_LeanTsTest_Vectors_spackE: spackE,
  l_LeanTsTest_Vectors_spackF: spackF,
  l_LeanTsTest_Vectors_spackG: spackG,
  l_LeanTsTest_Vectors_spackSum: spackSum,
  lean_int8_to_int: i8ToInt,
  lean_int16_to_int: i16ToInt,
  lean_int32_to_int: i32ToInt,
  lean_int64_to_int_sint: i64ToInt,
  l_LeanTsTest_Vectors_chainHead: chainHead,
  l_LeanTsTest_Vectors_pingN: pingN,
  l_LeanTsTest_Vectors_ftan: ftan,
  l_LeanTsTest_Vectors_fasin: fasin,
  l_LeanTsTest_Vectors_facos: facos,
  l_LeanTsTest_Vectors_fatan: fatan,
  l_LeanTsTest_Vectors_fatan2: fatan2,
  l_LeanTsTest_Vectors_fsinh: fsinh,
  l_LeanTsTest_Vectors_fcosh: fcosh,
  l_LeanTsTest_Vectors_ftanh: ftanh,
  l_LeanTsTest_Vectors_fexp2: fexp2,
  l_LeanTsTest_Vectors_flog2: flog2,
  l_LeanTsTest_Vectors_flog10: flog10,
  l_LeanTsTest_Vectors_fcbrt: fcbrt,
  l_LeanTsTest_Vectors_ftoBits: ftoBits,
  l_LeanTsTest_Vectors_fofBits: fofBits,
  l_LeanTsTest_Vectors_ffrExpM: ffrExpM,
  l_LeanTsTest_Vectors_ffrExpE: ffrExpE,
  l_LeanTsTest_Vectors_f32tan: f32tan,
  l_LeanTsTest_Vectors_f32exp: f32exp,
  l_LeanTsTest_Vectors_f32log: f32log,
  l_LeanTsTest_Vectors_f32cbrt: f32cbrt,
  l_LeanTsTest_Vectors_f32toBits: f32toBits,
  l_LeanTsTest_Vectors_nbits: nbits,
  l_LeanTsTest_Vectors_uszOfU64: uszOfU64,
  l_LeanTsTest_Vectors_uszAdd: uszAdd,
  l_LeanTsTest_Vectors_uszCompl: uszCompl,
  l_LeanTsTest_Vectors_uszToNat: uszToNat,
  l_LeanTsTest_HigherOrder_hofApply: hofApply,
  l_LeanTsTest_HigherOrder_listMapLam: listMapLam,
  l_LeanTsTest_HigherOrder_listFilterLam: listFilterLam,
  l_LeanTsTest_HigherOrder_listFoldlLam: listFoldlLam,
  l_LeanTsTest_HigherOrder_arrMapLam: arrMapLam,
  l_LeanTsTest_HigherOrder_applyAdders: applyAdders,
  l_LeanTsTest_HigherOrder_currySplit: currySplit,
  l_LeanTsTest_HigherOrder_optSeq: optSeq,
  l_LeanTsTest_HigherOrder_exSeq: exSeq,
  l_LeanTsTest_HigherOrder_fmapList: fmapList,
  l_LeanTsTest_HigherOrder_safeDivStr: safeDivStr,
  l_LeanTsTest_HigherOrder_hmDemo: hmDemo,
  l_LeanTsTest_HigherOrder_cpsCount: cpsCount,
  l_LeanTsTest_HigherOrder_cpsSum: cpsSum,
  l_LeanTsTest_Vectors_TodoList_add: add,
  l_LeanTsTest_Vectors_TodoList_toggle: toggle,
  l_LeanTsTest_Vectors_TodoList_remove: remove,
  l_LeanTsTest_Vectors_TodoList_step: step,
} = m

// Lean's Float.toString uses C `%f` (6 decimals); route through the generated
// floatStr so the harness exercises the real runtime renderer (NaN/Inf/-0.0).
const leanFloatToString = (x) => floatStr(x)

// Point = { tag:0, fields:[x,y] }
const P = (x, y) => ({ tag: 0, fields: [x, y] })
const showP = (p) => `(${show(p.fields[0])},${show(p.fields[1])})`

console.log(`double 0 = ${show(double(0n))}`)
console.log(`double 7 = ${show(double(7n))}`)
console.log(`double 1000000 = ${show(double(1000000n))}`)
console.log(`mkShifted(3,4) = ${show(showP(mkShifted(P(3n, 4n))))}`)
console.log(`mkShifted(0,0) = ${show(showP(mkShifted(P(0n, 0n))))}`)
console.log(`mkShifted(10,100) = ${show(showP(mkShifted(P(10n, 100n))))}`)
console.log(`sumTo 0 = ${show(sumTo(0n))}`)
console.log(`sumTo 5 = ${show(sumTo(5n))}`)
console.log(`sumTo 100 = ${show(sumTo(100n))}`)
console.log(`sumTo 100000 = ${show(sumTo(100000n))}`)
console.log(`fact 0 = ${show(fact(0n))}`)
console.log(`fact 5 = ${show(fact(5n))}`)
console.log(`fact 10 = ${show(fact(10n))}`)

// ---- Mixed ctor (object + packed sub-word scalars) ----
// Lean's layout pass packs region S as: d:UInt16 @0, b:UInt8 @2, c:UInt8 @3
// (alignment-driven). Reading those byte offsets returns the fields distinctly,
// where a single fields[] keyed by word-slot index would have collided them.
const mx = mkMixed(100n, 7, 9, 1000)
console.log(`mixed b = ${show(mx.sdata.getUint8(2))}`)
console.log(`mixed c = ${show(mx.sdata.getUint8(3))}`)
console.log(`mixed d = ${show(mx.sdata.getUint16(0, true))}`)
console.log(`mixedSum = ${show(mixedSum(mx))}`)
const m2 = mkMixed(0n, 255, 1, 65535)
console.log(`mixed2 b = ${show(m2.sdata.getUint8(2))}`)
console.log(`mixed2 c = ${show(m2.sdata.getUint8(3))}`)
console.log(`mixed2 d = ${show(m2.sdata.getUint16(0, true))}`)
console.log(`mixedSum2 = ${show(mixedSum(m2))}`)

// ---- Numeric tower: UInt wrap, Int Euclidean div/mod, Float ----
console.log(`u32wrap = ${show(u32wrap(4000000000, 1000000000))}`)
console.log(`u8wrap = ${show(u8wrap(3, 10))}`)
console.log(`intEdiv = ${show(intEdiv(-12n, 7n))}`)
console.log(`intEmod = ${show(intEmod(-12n, 7n))}`)
console.log(`intEdiv2 = ${show(intEdiv(12n, -7n))}`)
console.log(`intEmod2 = ${show(intEmod(12n, -7n))}`)
console.log(`intNeg = ${show(intNeg(42n))}`)
console.log(`floatCalc = ${show(leanFloatToString(floatCalc(3.0, 4.0)))}`)

// ---- String UTF-8 byte semantics over a multibyte (Japanese) string ----
const jp = "あいう" // each char is 3 UTF-8 bytes; length=3 code points, 9 bytes
console.log(`strLen = ${show(strLen(jp))}`)
console.log(`strBytes = ${show(strBytes(jp))}`)
console.log(`strGet0 = ${show(String.fromCodePoint(strGet0(jp)))}`)
console.log(`strGet1 = ${show(String.fromCodePoint(strGet1(jp)))}`)
console.log(`strExtract03 = ${show(strExtract(jp, 0n, 3n))}`)
console.log(`strExtract39 = ${show(strExtract(jp, 3n, 9n))}`)
console.log(
  `strLt = ${[
    ["abc", "abd"],
    ["ab", "abc"],
    ["b", "a"],
    ["a", "a"],
    ["\uFF61", "😀"],
    ["😀", "\uFF61"],
  ]
    .map(([a, b]) => (strLt(a, b) ? "true" : "false"))
    .join(" ")}`,
)

// ---- Array / List operations ----
// Lean prints Array as `#[a, b, ...]`, List as `[a, b, ...]`.
const showArr = (a) => `#[${show(a.join(", "))}]`
const listToArr2 = (l) => {
  const out = []
  let cur = l
  while (typeof cur !== "number" && cur.tag === 1) {
    out.push(cur.fields[0])
    cur = cur.fields[1]
  }
  return out
}
const showLst = (l) => `[${show(listToArr2(l).join(", "))}]`
// List literal: nil = 0, cons = {tag:1, fields:[head, tail]}
const lst2list = (arr) => arr.reduceRight((tl, h) => ({ tag: 1, fields: [h, tl] }), 0)
const arr = [1n, 2n, 3n, 4n, 5n]
console.log(`arrSum = ${show(arrSum(arr))}`)
console.log(`arrMapSum = ${show(arrMapSum(arr))}`)
console.log(`arrRange = ${show(showArr(arrRange(5n)))}`)
console.log(`arrGetD2 = ${show(arrGetD(arr, 2n))}`)
console.log(`arrGetD9 = ${show(arrGetD(arr, 9n))}`)
console.log(`arrAppend = ${show(showArr(arrAppend(arr, [6n, 7n])))}`)
const lst = lst2list([10n, 20n, 30n])
console.log(`listSum = ${show(listSum(lst))}`)
console.log(`listLen = ${show(listLen(lst))}`)
console.log(`listRev = ${show(showLst(listRev(lst)))}`)
console.log(`listMapSum = ${show(listMapSum(lst))}`)

// ---- Mutual / cross-function TCO (Bool prints as true/false; scalar 0/1) ----
const showBool = (b) => (b ? "true" : "false")
console.log(`parityEven 7 = ${show(showBool(parityEven(7n)))}`)
console.log(`parityOdd 7 = ${show(showBool(parityOdd(7n)))}`)
console.log(`parityEven 3000 = ${show(showBool(parityEven(3000n)))}`)
console.log(`parityOdd 3000 = ${show(showBool(parityOdd(3000n)))}`)
console.log(`cycle3 0 = ${show(cycle3(0n))}`)
console.log(`cycle3 1 = ${show(cycle3(1n))}`)
console.log(`cycle3 2 = ${show(cycle3(2n))}`)
console.log(`cycle3 3000 = ${show(cycle3(3000n))}`)

// ---- Signed fixed-width ints (Int8/16/32: unsigned bit pattern numbers, read through toInt) ----
const i8 = (v) => L.lean_int8_of_int(v)
const i16 = (v) => L.lean_int16_of_int(v)
const i32 = (v) => L.lean_int32_of_int(v)
console.log(`i8wrap = ${show(i8ToInt(i8wrap(i8(127n), i8(1n))))}`)
console.log(`i8neg = ${show(i8ToInt(i8neg(i8(-128n))))}`)
console.log(`i8div = ${show(i8ToInt(i8div(i8(-128n), i8(-1n))))}`)
console.log(`i8div0 = ${show(i8ToInt(i8div(i8(5n), i8(0n))))}`)
console.log(`i8mod = ${show(i8ToInt(i8mod(i8(-7n), i8(2n))))}`)
console.log(`i8mod2 = ${show(i8ToInt(i8mod(i8(7n), i8(-2n))))}`)
console.log(`i8shr = ${show(i8ToInt(i8shr(i8(-8n), i8(1n))))}`)
console.log(`i16wrap = ${show(i16ToInt(i16wrap(i16(256n), i16(256n))))}`)
console.log(`i32wrap = ${show(i32ToInt(i32wrap(i32(2147483647n), i32(1n))))}`)
console.log(`i64mul = ${show(i64mul(4294967296n, 4294967296n))}`)
console.log(`i8toInt = ${show(i8toInt(i8(-5n)))}`)
console.log(`i32toInt = ${show(i32toInt(i32(-100n)))}`)

// ---- Float / Float32 toString edge cases ----
console.log(`fstr0 = ${show(floatStr(0.0))}`)
console.log(`fstrPi = ${show(floatStr(3.14))}`)
console.log(`fstrNeg0 = ${show(floatStr(-0.0))}`)
console.log(`fstrInf = ${show(floatStr(1.0 / 0.0))}`)
console.log(`fstrNInf = ${show(floatStr(-1.0 / 0.0))}`)
console.log(`fstrNaN = ${show(floatStr(0.0 / 0.0))}`)
console.log(`fstrBig = ${show(floatStr(123456789.12345679))}`)
console.log(`fstr1e20 = ${show(floatStr(1e20))}`)
console.log(`fstr1e21 = ${show(floatStr(1e21))}`)
console.log(`fstrNeg = ${show(floatStr(-2.5))}`)
console.log(`f32str = ${show(float32Str(16777217.0))}`)
console.log(`f32strPi = ${show(float32Str(3.14))}`)

// ---- Packed signed-scalar fields (Int8/16/32/64) + Float/Float32 in region S ----
// Stored via the unsigned/float DataView setters (no signed IRType at 4.35.0);
// the signed value is recovered at the toInt boundary (lean_int*_to_int), which
// is exactly how Lean's compiled code reinterprets the raw uintN bytes. Floats
// are exact. spackSum returns Int, so it reinterprets all four signed fields.
const sp = mkSPack(100n, i8(-5n), i16(-300n), i32(-70000n), -5000000000n, -2.5, 1.5)
console.log(`spackA = ${show(i8ToInt(spackA(sp)))}`)
console.log(`spackB = ${show(i16ToInt(spackB(sp)))}`)
console.log(`spackC = ${show(i32ToInt(spackC(sp)))}`)
console.log(`spackE = ${show(i64ToInt(spackE(sp)))}`)
console.log(`spackF = ${show(floatStr(spackF(sp)))}`)
console.log(`spackG = ${show(float32Str(spackG(sp)))}`)
console.log(`spackSum = ${show(spackSum(sp))}`)

// ---- Higher-order / closure / typeclass / exception (HigherOrder) ----
// Option Nat: none = 0, some x = { tag:1, fields:[x] }. Lean prints
// `none`/`some x`. Except ε α: error = tag 0, ok = tag 1; Lean prints
// `Except.error e`/`Except.ok v` via its Repr.
const showOpt = (o) => (typeof o === "number" ? "none" : `(some ${show(o.fields[0])})`)
const showExc = (e) => (e.tag === 1 ? `ok: ${show(e.fields[0])}` : `error: ${show(e.fields[0])}`)
console.log(`hofApply = ${show(hofApply())}`)
console.log(`listMapLam = ${show(showLst(listMapLam(lst2list([1n, 2n, 3n]))))}`)
console.log(`listFilterLam = ${show(showLst(listFilterLam(lst2list([1n, 2n, 3n, 4n]))))}`)
console.log(`listFoldlLam = ${show(listFoldlLam(lst2list([1n, 2n, 3n])))}`)
console.log(`arrMapLam = ${show(showArr(arrMapLam([1n, 2n, 3n])))}`)
console.log(`applyAdders = ${show(applyAdders(5n))}`)
console.log(`currySplit = ${show(currySplit(1n))}`)
console.log(`optSeq = ${show(showOpt(optSeq()))}`)
console.log(`exSeq = ${show(showExc(exSeq()))}`)
console.log(`fmapList = ${show(showLst(fmapList(lst2list([1n, 2n, 3n]))))}`)
console.log(`safeDiv 10 2 = ${show(safeDivStr(10n, 2n))}`)
console.log(`safeDiv 10 0 = ${show(safeDivStr(10n, 0n))}`)
console.log(`hmDemo = ${show(hmDemo())}`)
console.log(`cpsCount = ${show(cpsCount(10000n))}`)
console.log(`cpsSum = ${show(cpsSum(50000n))}`)
console.log(`chainHead 10 = ${show(chainHead(10n))}`)
console.log(`pingN 5 0 = ${show(pingN(5n, 0n))}`)
console.log(`ftan = ${show(floatStr(ftan(1.0)))}`)
console.log(`fasin = ${show(floatStr(fasin(0.5)))}`)
console.log(`facos = ${show(floatStr(facos(0.5)))}`)
console.log(`fatan = ${show(floatStr(fatan(2.0)))}`)
console.log(`fatan2 = ${show(floatStr(fatan2(1.0, 2.0)))}`)
console.log(`fsinh = ${show(floatStr(fsinh(1.0)))}`)
console.log(`fcosh = ${show(floatStr(fcosh(1.0)))}`)
console.log(`ftanh = ${show(floatStr(ftanh(1.0)))}`)
console.log(`fexp2 = ${show(floatStr(fexp2(10.0)))}`)
console.log(`flog2 = ${show(floatStr(flog2(1024.0)))}`)
console.log(`flog10 = ${show(floatStr(flog10(1000.0)))}`)
console.log(`fcbrt = ${show(floatStr(fcbrt(27.0)))}`)
console.log(`ftoBits = ${show(ftoBits(1.0))}`)
console.log(`fofBits = ${show(floatStr(fofBits(4607182418800017408n)))}`)
console.log(`ffrExpM = ${show(floatStr(ffrExpM(12.0)))}`)
console.log(`ffrExpE = ${show(ffrExpE(12.0))}`)
console.log(`f32tan = ${show(float32Str(f32tan(1.0)))}`)
console.log(`f32exp = ${show(float32Str(f32exp(2.0)))}`)
console.log(`f32log = ${show(float32Str(f32log(10.0)))}`)
console.log(`f32cbrt = ${show(float32Str(f32cbrt(27.0)))}`)
console.log(`f32toBits = ${show(f32toBits(1.0))}`)
console.log(`nbits = ${show(nbits())}`)
console.log(`uszOfU64 = ${show(uszToNat(uszOfU64(4294967296n)))}`)
console.log(`uszAddWrap = ${show(uszToNat(uszAdd(0xffffffffffffffffn, 1n)))}`)
console.log(`uszCompl = ${show(uszToNat(uszCompl(0n)))}`)

// ---- TodoList JS model ----
// List: nil = 0, cons = { tag:1, fields:[head, tail] }
// Todo: { tag:0, fields:[id, title, done] }   (done is scalar 0/1)
// TodoList: { tag:0, fields:[items, nextId] }
// Command: add(title)=tag0, toggle(id)=tag1, remove(id)=tag2
const empty = { tag: 0, fields: [0, 0n] }
const Cadd = (title) => ({ tag: 0, fields: [title] })
const Ctoggle = (id) => ({ tag: 1, fields: [id] })
const Cremove = (id) => ({ tag: 2, fields: [id] })

const listToArr = (l) => {
  const out = []
  let cur = l
  while (typeof cur !== "number" && cur.tag === 1) {
    out.push(cur.fields[0])
    cur = cur.fields[1]
  }
  return out
}
// Todo: { tag:0, fields:[id, title], sdata:[done:u8 @0] } — done is a packed
// scalar in region S, read via the byte-addressed DataView (sproj layout).
const showTodo = (t) =>
  `${show(t.fields[0])}:${show(t.fields[1])}:${show(t.sdata.getUint8(0) ? "x" : " ")}`
const showList = (l) => "[" + listToArr(l.fields[0]).map(showTodo).join(",") + "]@" + l.fields[1]

const l1 = add(empty, "buy milk")
console.log(`add1 = ${show(showList(l1))}`)
const l2 = add(l1, "walk dog")
console.log(`add2 = ${show(showList(l2))}`)
const l3 = add(l2, "write code")
console.log(`add3 = ${show(showList(l3))}`)
const l4 = toggle(l3, 1n)
console.log(`toggle1 = ${show(showList(l4))}`)
const l5 = toggle(l4, 0n)
console.log(`toggle0 = ${show(showList(l5))}`)
const l6 = remove(l5, 1n)
console.log(`remove1 = ${show(showList(l6))}`)
const l7 = step(l6, Cadd("new task"))
console.log(`step-add = ${show(showList(l7))}`)
const l8 = step(l7, Ctoggle(2n))
console.log(`step-toggle = ${show(showList(l8))}`)
const l9 = step(l8, Cremove(0n))
console.log(`step-remove = ${show(showList(l9))}`)
