import { defineConfig, type ViteUserConfig } from "vite-plus"

const config: ViteUserConfig = defineConfig({
  fmt: {
    semi: false,
    singleQuote: false,
    trailingComma: "all",
    sortPackageJson: false,
    ignorePatterns: ["lake-manifest.json"],
  },
  lint: {
    categories: { correctness: "error", suspicious: "warn" },
    ignorePatterns: ["node_modules", "dist", ".direnv", ".lake"],
    options: { typeAware: true, typeCheck: true },
  },
  test: {
    include: ["test/**/*.test.ts"],
  },
  pack: [
    {
      entry: {
        runtime: "src/runtime/index.ts",
        "runtime/node": "src/runtime/node.ts",
      },
      platform: "neutral",
      format: "esm",
      dts: true,
    },
  ],
  run: {
    tasks: {
      check: { command: "vp check && vp test" },
    },
  },
})

export default config
