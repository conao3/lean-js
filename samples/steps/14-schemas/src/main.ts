import { checkModel } from "lean-ts/verify"
import { withdraw } from "./account.ts"

console.log(
  withdraw({ owner: "ann", balance: 100 }, 30),
  withdraw({ owner: "ann", balance: 100 }, 300),
)
await checkModel(withdraw, { seed: 1 })
console.log("checkModel: withdraw stays within the limits of Account")
