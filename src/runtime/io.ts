import type { Ctor, Fn, Obj } from "./object.ts"
import {
  asBytes,
  asCtor,
  asHandle,
  asRef,
  asString,
  lean_apply,
  lean_ctor,
  lean_tag,
  lean_trampoline,
} from "./object.ts"
import { decodeUtf8, encodeUtf8 } from "./string.ts"

// The OS surface the IO externs need. `index.ts` installs the Node platform
// (`node.ts`) when `process.getBuiltinModule` is available; elsewhere (a
// browser) the default platform writes stdout/stderr to the console and every
// other OS operation returns `IO.Error.unsupportedOperation`.
export interface Platform {
  target: string
  writeStdout(data: string | Uint8Array): void
  writeStderr(data: string | Uint8Array): void
  // Reads up to `buf.length` bytes from `fd` into `buf`; 0 is end of file.
  readFd(fd: number, buf: Uint8Array): number
  writeFd(fd: number, data: Uint8Array): void
  openFile(path: string, flags: string): number
  isTty(fd: number): boolean
  getenv(name: string): string | undefined
  argv(): string[]
  exit(code: number): never
  setExitCode(code: number): void
}

function consoleWriter(log: (s: string) => void): (data: string | Uint8Array) => void {
  let pending = ""
  return (data) => {
    pending += typeof data === "string" ? data : decodeUtf8(data)
    const nl = pending.lastIndexOf("\n")
    if (nl >= 0) {
      log(pending.slice(0, nl))
      pending = pending.slice(nl + 1)
    }
  }
}

function unsupported(op: string): never {
  const e = new Error(`${op} is not supported on ${platform.target}`)
  e.name = "UnsupportedOperation"
  throw e
}

export const browserPlatform: Platform = {
  target: "browser",
  writeStdout: consoleWriter((s) => console.log(s)),
  writeStderr: consoleWriter((s) => console.error(s)),
  readFd: () => unsupported("reading a file descriptor"),
  writeFd: () => unsupported("writing a file descriptor"),
  openFile: () => unsupported("opening a file"),
  isTty: () => false,
  getenv: () => undefined,
  argv: () => [],
  exit: () => unsupported("exiting the process"),
  setExitCode: () => {},
}

let platform: Platform = browserPlatform

export function setPlatform(p: Platform): void {
  platform = p
}

export function getPlatform(): Platform {
  return platform
}

// ---- panic (matches runtime/object.cpp lean_panic_fn) ----
// `panicCore`/`panic`/`panic!`/`unreachable!` compile to a call to
// `lean_panic_fn(default_val, msg)`: it prints the message to stderr (unless
// suppressed), then RETURNS the Inhabited default — it does NOT abort or exit by
// default, so the program stays logically total and continues. Mutable flags
// mirror the C globals.
let panicMessages = true
let exitOnPanic = false

export function lean_set_panic_messages(b: number): void {
  panicMessages = b !== 0
}

export function lean_set_exit_on_panic(b: number): void {
  exitOnPanic = b !== 0
}

export function lean_panic_fn<T>(defaultVal: T, msg: Obj): T {
  if (panicMessages) platform.writeStderr(asString(msg) + "\n")
  if (exitOnPanic) platform.exit(1)
  return defaultVal
}

export function lean_panic_fn_borrowed<T>(defaultVal: T, msg: Obj): T {
  return lean_panic_fn(defaultVal, msg)
}

// FnBody.unreachable -> lean_internal_panic_unreachable: FATAL. Dead match arms
// are never meant to run; print and terminate (never fall through).
export function lean_internal_panic(msg: string): never {
  platform.writeStderr("INTERNAL PANIC: " + msg + "\n")
  return platform.exit(1)
}

export function lean_internal_panic_unreachable(): never {
  return lean_internal_panic("unreachable code has been reached")
}

// ---- io_result ----
// Every compiled IO/BaseIO action is a function `(...args) => io_result`. The
// `World` token is an IR `void` param; the emitter drops void params, so actions
// receive NO trailing world arg (closure `app` sites do pass an erased
// `undefined`, which the runtime closures simply ignore). io_result mirrors
// `EST.Out` / `lean_io_result`: ok = ctor tag 0, error = ctor tag 1, each with
// one field.
export function lean_io_result_mk_ok(a: Obj): Ctor {
  return lean_ctor(0, 1, 0, 0, a)
}

export function lean_io_result_mk_error(e: Obj): Ctor {
  return lean_ctor(1, 1, 0, 0, e)
}

export function lean_io_result_is_ok(r: Obj): boolean {
  return lean_tag(r) === 0
}

export function lean_io_result_get_value(r: Obj): Obj {
  return asCtor(r).fields[0]
}

export function lean_io_result_get_error(r: Obj): Obj {
  return asCtor(r).fields[0]
}

// IO.Error.userError msg. userError is the last ctor of the IO.Error inductive
// (cidx 18); render via its message field.
const IO_ERROR_UNSUPPORTED_OPERATION = 4
const IO_ERROR_USER = 18

export function lean_mk_io_user_error(msg: Obj): Ctor {
  return lean_ctor(IO_ERROR_USER, 1, 0, 0, msg)
}

// IO.Error.unsupportedOperation (osCode : UInt32) (details : String): the
// details string is the object field, the osCode the packed scalar.
export function lean_mk_io_error_unsupported_operation(details: string): Ctor {
  const e = lean_ctor(IO_ERROR_UNSUPPORTED_OPERATION, 1, 0, 4, details)
  e.sdata?.setUint32(0, 0, true)
  return e
}

function ioErrorOf(e: unknown): Ctor {
  if (e instanceof Error && e.name === "UnsupportedOperation")
    return lean_mk_io_error_unsupported_operation(e.message)
  return lean_mk_io_user_error(String(e instanceof Error ? e.message : e))
}

// Full IO.Error.toString matching `@[export lean_io_error_to_string]`
// (Init/System/IOError.lean): 19 constructors, cidx order
//   0 alreadyExists 1 otherError 2 resourceBusy 3 resourceVanished
//   4 unsupportedOperation 5 hardwareFault 6 unsatisfiedConstraints
//   7 illegalOperation 8 protocolError 9 timeExpired 10 interrupted
//   11 noFileOrDirectory 12 invalidArgument 13 permissionDenied
//   14 resourceExhausted 15 inappropriateType 16 noSuchThing
//   17 unexpectedEof (nullary) 18 userError.
// fopenErrorToString / otherErrorToString decapitalize the first char of the
// gist (and of `details` when present); osCode is a UInt32 (so -2 -> 4294967294).
function text(x: Obj): string {
  return typeof x === "string"
    ? x
    : typeof x === "number" || typeof x === "bigint"
      ? x.toString()
      : ""
}

function decap(s: Obj): string {
  const t = text(s)
  return t.length === 0 ? t : t.charAt(0).toLowerCase() + t.slice(1)
}

function ef(e: Obj, i: number): Obj {
  return typeof e === "object" && e !== null && "fields" in e ? e.fields[i] : undefined
}

// `Option String` field: none == 0 (number), some == {tag:1,fields:[s]}.
function optFn(o: Obj): Obj {
  return typeof o === "object" && o !== null && "fields" in o ? o.fields[0] : null
}

function ioDetails(code: Obj, details: Obj): string {
  return (
    " (error code: " +
    String(Number(code) >>> 0) +
    (details != null ? ", " + decap(details) : "") +
    ")"
  )
}

function ioFopen(gist: Obj, fn: Obj, code: Obj, details: Obj): string {
  return decap(gist) + ioDetails(code, details) + "\n  file: " + text(fn)
}

function ioOther(gist: Obj, code: Obj, details: Obj): string {
  return decap(gist) + ioDetails(code, details)
}

function withFile(gist: string, e: Obj): string {
  const fn = optFn(ef(e, 0))
  return fn != null ? ioFopen(gist, fn, ef(e, 1), ef(e, 2)) : ioOther(gist, ef(e, 1), ef(e, 2))
}

export function lean_io_error_to_string(e: Obj): string {
  switch (lean_tag(e)) {
    case 0:
      return withFile("already exists", e)
    case 1:
      return ioOther(ef(e, 1), ef(e, 0), null)
    case 2:
      return ioOther("resource busy", ef(e, 0), ef(e, 1))
    case 3:
      return ioOther("resource vanished", ef(e, 0), ef(e, 1))
    case 4:
      return ioOther("unsupported operation", asCtor(e).sdata?.getUint32(0, true) ?? 0, ef(e, 0))
    case 5:
      return ioOther("hardware fault", ef(e, 0), null)
    case 6:
      return ioOther("directory not empty", ef(e, 0), null)
    case 7:
      return ioOther("illegal operation", ef(e, 0), ef(e, 1))
    case 8:
      return ioOther("protocol error", ef(e, 0), ef(e, 1))
    case 9:
      return ioOther("time expired", ef(e, 0), ef(e, 1))
    case 10:
      return ioFopen("interrupted system call", ef(e, 0), ef(e, 1), ef(e, 2))
    case 11:
      return ioFopen("no such file or directory", ef(e, 0), ef(e, 1), null)
    case 12:
      return withFile("invalid argument", e)
    case 13: {
      const fn = optFn(ef(e, 0))
      const d = ef(e, 2)
      return fn != null ? ioFopen(d, fn, ef(e, 1), null) : ioOther(d, ef(e, 1), null)
    }
    case 14:
      return withFile("resource exhausted", e)
    case 15:
      return withFile("inappropriate type", e)
    case 16:
      return withFile("no such thing", e)
    case 17:
      return "end of file"
    case 18:
      return text(ef(e, 0))
    default:
      return text(e)
  }
}

// FS.Stream ctor: field order from `structure FS.Stream`
//   flush(0) read(1) write(2) getLine(3) putStr(4) isTty(5).
// Each field is itself an IO action closure: it takes its value args then an
// erased world arg, and returns an io_result. lean_apply invokes them.
function mkStream(fields: Fn[]): Ctor {
  return lean_ctor(0, 6, 0, 0, ...fields)
}

function mkWriteStream(write: (data: string | Uint8Array) => void): Ctor {
  return mkStream([
    () => lean_io_result_mk_ok(0),
    (_n: Obj) => lean_io_result_mk_ok(new Uint8Array(0)),
    (buf: Obj) => {
      write(asBytes(buf))
      return lean_io_result_mk_ok(0)
    },
    () => lean_io_result_mk_ok(""),
    (s: Obj) => {
      write(asString(s))
      return lean_io_result_mk_ok(0)
    },
    () => lean_io_result_mk_ok(0),
  ])
}

function readLine(fd: number): string {
  const bytes: number[] = []
  const one = new Uint8Array(1)
  for (;;) {
    if (platform.readFd(fd, one) === 0) break
    const c = one[0] ?? 0
    bytes.push(c)
    if (c === 0x0a) break
  }
  return decodeUtf8(Uint8Array.from(bytes))
}

function readBytes(fd: number, n: number): Uint8Array {
  const buf = new Uint8Array(n)
  const got = platform.readFd(fd, buf)
  return buf.slice(0, got)
}

function ioAction(act: () => Obj): Ctor {
  try {
    return lean_io_result_mk_ok(act())
  } catch (e) {
    return lean_io_result_mk_error(ioErrorOf(e))
  }
}

// Real fd-0 stdin stream. Lean getLine reads up to AND including the next '\n'
// ('' == EOF); read(n) reads up to n bytes (empty array == EOF, stream stays open).
function mkStdinStream(): Ctor {
  return mkStream([
    () => lean_io_result_mk_ok(0),
    (n: Obj) => ioAction(() => readBytes(0, Number(n))),
    (_b: Obj) => lean_io_result_mk_ok(0),
    () => ioAction(() => readLine(0)),
    (_s: Obj) => lean_io_result_mk_ok(0),
    () => lean_io_result_mk_ok(platform.isTty(0) ? 1 : 0),
  ])
}

let stdoutStream: Obj = mkWriteStream((x) => platform.writeStdout(x))
let stderrStream: Obj = mkWriteStream((x) => platform.writeStderr(x))
let stdinStream: Obj = mkStdinStream()

// getStdout/getStderr/getStdin are BaseIO actions: BaseIO cannot error, so its
// `EST.Out.ok` is erased and the extern returns the bare Stream (the consuming
// IR does `proj[4]` directly on the result). Likewise the set* variants return
// the previous stream directly.
export function lean_get_stdout(): Obj {
  return stdoutStream
}

export function lean_get_stderr(): Obj {
  return stderrStream
}

export function lean_get_stdin(): Obj {
  return stdinStream
}

export function lean_get_set_stdout(s: Obj): Obj {
  const p = stdoutStream
  stdoutStream = s
  return p
}

export function lean_get_set_stderr(s: Obj): Obj {
  const p = stderrStream
  stderrStream = s
  return p
}

export function lean_get_set_stdin(s: Obj): Obj {
  const p = stdinStream
  stdinStream = s
  return p
}

export function lean_io_eprint(s: Obj): Obj {
  platform.writeStderr(asString(s))
  return lean_io_result_mk_ok(0)
}

export function lean_io_eprintln(s: Obj): Obj {
  platform.writeStderr(asString(s) + "\n")
  return lean_io_result_mk_ok(0)
}

// IO.Ref / ST.Ref : a single mutable cell {value}. These are BaseIO actions
// (cannot error), so `EST.Out.ok` is erased and the externs return bare values
// (the consuming IR uses the result directly, never `case`-ing on a tag).
export function lean_st_mk_ref(a: Obj): Obj {
  return { value: a }
}

export function lean_st_ref_get(r: Obj): Obj {
  return asRef(r).value
}

export function lean_st_ref_set(r: Obj, a: Obj): Obj {
  asRef(r).value = a
  return 0
}

export function lean_st_ref_swap(r: Obj, a: Obj): Obj {
  const o = asRef(r).value
  asRef(r).value = a
  return o
}

export function lean_st_ref_take(r: Obj): Obj {
  const o = asRef(r).value
  asRef(r).value = undefined
  return o
}

export function lean_st_ref_put(r: Obj, a: Obj): Obj {
  return lean_st_ref_set(r, a)
}

export function lean_st_ref_ptr_eq(r1: Obj, r2: Obj): number {
  return r1 === r2 ? 1 : 0
}

// IO.getEnv : BaseIO (Option String). BaseIO -> bare Option (no io_result wrap).
// none = 0 (nullary), some = {tag:1,fields:[s]}.
export function lean_io_getenv(name: Obj): Obj {
  const v = platform.getenv(asString(name))
  return v === undefined ? 0 : lean_ctor(1, 1, 0, 0, v)
}

// IO.Process.exit / forceExit.
export function lean_io_exit(code: number): never {
  return platform.exit(code & 0xff)
}

export function lean_io_force_exit(code: number): never {
  return platform.exit(code & 0xff)
}

// FS.Handle primitives over the platform's file descriptors.
const MODE_FLAG = ["r", "w", "wx", "r+", "a"]

export function lean_io_prim_handle_mk(path: Obj, mode: number): Obj {
  return ioAction(() => ({ fd: platform.openFile(asString(path), MODE_FLAG[mode] ?? "r") }))
}

export function lean_io_prim_handle_put_str(h: Obj, s: Obj): Obj {
  return ioAction(() => {
    platform.writeFd(asHandle(h).fd, encodeUtf8(asString(s)))
    return 0
  })
}

export function lean_io_prim_handle_write(h: Obj, buf: Obj): Obj {
  return ioAction(() => {
    platform.writeFd(asHandle(h).fd, asBytes(buf))
    return 0
  })
}

export function lean_io_prim_handle_read(h: Obj, n: bigint): Obj {
  return ioAction(() => readBytes(asHandle(h).fd, Number(n)))
}

export function lean_io_prim_handle_flush(_h: Obj): Obj {
  return lean_io_result_mk_ok(0)
}

export function lean_io_prim_handle_is_tty(_h: Obj): Obj {
  return lean_io_result_mk_ok(0)
}

// Handle.getLine: read up to and including the next '\n' from the handle's fd
// ('' == EOF). Byte-loop then UTF-8 decode, matching Lean's line semantics.
export function lean_io_prim_handle_get_line(h: Obj): Obj {
  return ioAction(() => readLine(asHandle(h).fd))
}

// lean_io_result_show_error analogue: matches the C runtime which prints, to
// stderr, "uncaught exception: " + IO.Error.toString(err) + "\n".
export function lean_io_result_show_error(res: Obj): void {
  platform.writeStderr(
    "uncaught exception: " + lean_io_error_to_string(lean_io_result_get_error(res)) + "\n",
  )
}

// ---- dbgTrace / dbgTraceIfShared / dbgSleep ----
// lean_dbg_trace(s, fn): write s + '\n' to stderr, then force the thunk `fn`
// applied to Unit.
export function lean_dbg_trace(s: Obj, fn: Obj): Obj {
  platform.writeStderr(asString(s) + "\n")
  return lean_trampoline(lean_apply(fn, [0]))
}

// dbgTraceIfShared (s) (a): prints s only if `a` is RC-shared (RC(a) > 1). Its
// second arg is the VALUE `a` itself (not a thunk), and it returns `a`. Refcount
// is not modeled under JS GC, so a value is never "shared" in the RC sense:
// never print, just return `a` -- observably identical to native here.
export function lean_dbg_trace_if_shared(_s: Obj, a: Obj): Obj {
  return a
}

// A millisecond sleep is not observable in program output; just force the thunk.
export function lean_dbg_sleep(_ms: number, fn: Obj): Obj {
  return lean_trampoline(lean_apply(fn, [0]))
}

// ---- pointer utilities (the SAFE surface is observationally pure) ----
// withPtrAddr's proof obligation (∀ u1 u2, k u1 = k u2) guarantees the result is
// address-independent, so a constant address is faithful for every safe caller.
export function lean_ptr_addr(_a: Obj): bigint {
  return 0n
}

// isExclusiveUnsafe: no RC in JS; report non-exclusive (0) so copy-on-write paths
// stay value-correct.
export function lean_is_exclusive_obj(_a: Obj): number {
  return 0
}

// ---- module-initialization chain (emitInitFn / emitDeclInit analogue) ----
// EmitC emits, per module, an init fn that runs each decl's init: @[init] IO
// Unit actions and closed-term global initializers, short-circuiting on the
// first IOResult error. We mirror that with a thunk registry. Each registered
// thunk returns an io_result (ok = value already assigned to its global inside
// the thunk; error = mk_error). The initialized guard makes it idempotent.
const initThunks: (() => Obj)[] = []
let initialized = false

export function lean_register_init(thunk: () => Obj): void {
  initThunks.push(thunk)
}

export function lean_run_init(): Obj {
  if (initialized) return lean_io_result_mk_ok(0)
  initialized = true
  for (const t of initThunks) {
    const res = t()
    if (!lean_io_result_is_ok(res)) return res
  }
  return lean_io_result_mk_ok(0)
}

// Entry point: run a compiled `main`, decode the io_result like C `main`.
// `mainFn` already has its void world param dropped (the emitter omits it), so
// arity-1 IO actions are invoked with no args; arity-2 (`List String -> IO X`)
// receives the argv-derived List. `retIsU32` picks the exit-code expression.
// Module init runs first (mirrors emitMainFn): an init-time IOResult error
// flows through the SAME show-error + exit-1 path as a main-time error.
export function lean_run_main(mainFn: Fn, hasArgs: boolean, retIsU32: boolean): void {
  let res = lean_run_init()
  if (lean_io_result_is_ok(res)) {
    if (hasArgs) {
      const args = platform.argv().reduceRight<Obj>((tl, s) => lean_ctor(1, 2, 0, 0, s, tl), 0)
      res = Reflect.apply(mainFn, undefined, [args])
    } else {
      res = Reflect.apply(mainFn, undefined, [])
    }
  }
  if (lean_io_result_is_ok(res)) {
    const v = lean_io_result_get_value(res)
    platform.setExitCode(retIsU32 ? Number(v) & 0xff : 0)
  } else {
    lean_io_result_show_error(res)
    platform.setExitCode(1)
  }
}
