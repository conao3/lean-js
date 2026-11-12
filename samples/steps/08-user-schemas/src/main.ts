import { Account, bank } from "./code.ts"

const [a, b] = bank.transfer({ owner: "ann", balance: 100 }, { owner: "bob", balance: 5 }, 30)
console.log(JSON.stringify(a), JSON.stringify(b), Account.safeParse(a).success)
console.log(JSON.stringify(bank.transfer(a, b, 1000)))
console.log(JSON.stringify(bank.transfer(a, { owner: "cy", balance: 999_990 }, 20)))
try {
  bank.transfer({ owner: "", balance: 1 }, b, 1)
} catch (e) {
  if (e instanceof Error) console.log("rejected:", e.name, e.message)
}
