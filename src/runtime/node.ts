import type * as fs from "node:fs"
import type { Platform } from "./io.ts"

function isEof(e: unknown): boolean {
  if (!(e instanceof Error) || !("code" in e)) return false
  return e.code === "EOF" || e.code === "EAGAIN"
}

// The Node platform: std streams through `process`, file descriptors through
// `node:fs` (synchronous). `node:fs` is resolved lazily through
// `process.getBuiltinModule`, so importing this module never touches Node APIs.
export function nodePlatform(): Platform {
  let fsCache: typeof fs | null = null
  const nodeFs = (): typeof fs => {
    fsCache ??= process.getBuiltinModule("node:fs")
    return fsCache
  }
  return {
    target: "node",
    writeStdout: (data) => {
      process.stdout.write(data)
    },
    writeStderr: (data) => {
      process.stderr.write(data)
    },
    readFd: (fd, buf) => {
      try {
        return nodeFs().readSync(fd, buf, 0, buf.length, null)
      } catch (e) {
        if (isEof(e)) return 0
        throw e
      }
    },
    writeFd: (fd, data) => {
      nodeFs().writeSync(fd, data)
    },
    openFile: (path, flags) => nodeFs().openSync(path, flags),
    isTty: (fd) => fd === 0 && process.stdin.isTTY,
    getenv: (name) => process.env[name],
    argv: () => process.argv.slice(2),
    exit: (code) => process.exit(code),
    setExitCode: (code) => {
      process.exitCode = code
    },
  }
}
