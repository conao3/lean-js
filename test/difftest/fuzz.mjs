import { readFileSync } from "node:fs"
import * as fuzz from "../../test-out/fuzz.ts"

const show = (x) => String(x)

const m = fuzz

// List Nat: nil = scalar 0, cons = { tag:1, fields:[head, tail] } (head first).
const mkList = (arr) => arr.reduceRight((tl, h) => ({ tag: 1, fields: [h, tl] }), 0)
// Mirror LeanTsTest.Fuzz.unescape (replace order: \t, \n, then \\).
const unesc = (s) => s.replace(/\\t/g, "\t").replace(/\\n/g, "\n").replace(/\\\\/g, "\\")

const lines = readFileSync(0, "utf8")
  .split("\n")
  .filter((l) => l.length > 0)
const out = []
for (const line of lines) {
  const p = line.split("\t")
  switch (p[0]) {
    case "NAT":
      out.push(`NAT\t${show(m.l_LeanTsTest_Fuzz_fNat(BigInt(p[1])))}`)
      break
    case "INT":
      out.push(`INT\t${show(m.l_LeanTsTest_Fuzz_fInt(BigInt(p[1]), BigInt(p[2])))}`)
      break
    case "U32":
      out.push(`U32\t${show(m.l_LeanTsTest_Fuzz_fU32(Number(p[1]) >>> 0, Number(p[2]) >>> 0))}`)
      break
    case "U8":
      out.push(`U8\t${show(m.l_LeanTsTest_Fuzz_fU8(Number(p[1]) & 255, Number(p[2]) & 255))}`)
      break
    case "STR":
      out.push(`STR\t${show(m.l_LeanTsTest_Fuzz_fStr(unesc(p[1] ?? "")))}`)
      break
    case "HASH":
      out.push(`HASH\t${show(m.l_LeanTsTest_Fuzz_fHash(unesc(p[1] ?? "")))}`)
      break
    case "LNAT":
      out.push(
        `LNAT\t${show(
          m.l_LeanTsTest_Fuzz_fListNat(
            mkList(
              p
                .slice(1)
                .filter((x) => x)
                .map(BigInt),
            ),
          ),
        )}`,
      )
      break
    case "ANAT":
      out.push(
        `ANAT\t${show(
          m.l_LeanTsTest_Fuzz_fArrNat(
            p
              .slice(1)
              .filter((x) => x)
              .map(BigInt),
          ),
        )}`,
      )
      break
    default:
      out.push(`ERR\t${show(line)}`)
      break
  }
}
process.stdout.write(out.join("\n") + (out.length ? "\n" : ""))
