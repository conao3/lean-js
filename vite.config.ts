import { defineConfig, type ViteUserConfig } from "vite-plus"

const config: ViteUserConfig = defineConfig({
  fmt: {
    semi: false,
    singleQuote: false,
    trailingComma: "all",
    sortPackageJson: false,
    ignorePatterns: ["lake-manifest.json", "**/_lean/**", "**/.lean-ts/**"],
  },
  lint: {
    categories: { correctness: "error", suspicious: "warn" },
    ignorePatterns: ["node_modules", "dist", ".direnv", ".lake"],
    options: { typeAware: true, typeCheck: true },
  },
  test: {
    include: ["test/**/*.test.ts"],
    exclude: ["test/embed/**", "node_modules/**"],
  },
  pack: [
    {
      entry: {
        index: "src/index.ts",
        runtime: "src/runtime/index.ts",
        "runtime/node": "src/runtime/node.ts",
        schema: "src/schema/index.ts",
        cli: "src/cli.ts",
      },
      platform: "neutral",
      format: "esm",
      dts: true,
      deps: { neverBundle: [/^node:/u] },
    },
  ],
  run: {
    tasks: {
      check: { command: "vp check && vp test" },
    },
  },
})

export default config
