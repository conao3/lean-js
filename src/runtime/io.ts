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
const IO_ERROR_ALREADY_EXISTS = 0
const IO_ERROR_OTHER = 1
const IO_ERROR_RESOURCE_BUSY = 2
const IO_ERROR_RESOURCE_VANISHED = 3
const IO_ERROR_UNSUPPORTED_OPERATION = 4
const IO_ERROR_HARDWARE_FAULT = 5
const IO_ERROR_UNSATISFIED_CONSTRAINTS = 6
const IO_ERROR_ILLEGAL_OPERATION = 7
const IO_ERROR_PROTOCOL = 8
const IO_ERROR_TIME_EXPIRED = 9
const IO_ERROR_INTERRUPTED = 10
const IO_ERROR_NO_FILE_OR_DIRECTORY = 11
const IO_ERROR_INVALID_ARGUMENT = 12
const IO_ERROR_PERMISSION_DENIED = 13
const IO_ERROR_RESOURCE_EXHAUSTED = 14
const IO_ERROR_INAPPROPRIATE_TYPE = 15
const IO_ERROR_NO_SUCH_THING = 16
const IO_ERROR_USER = 18

export function lean_mk_io_user_error(msg: Obj): Ctor {
  return lean_ctor(IO_ERROR_USER, 1, 0, 0, msg)
}

// An IO.Error with an OS code: the filename (a `String` for interrupted and
// noFileOrDirectory, an `Option String` for alreadyExists and invalidArgument
// to noSuchThing) and the details string are the object fields, the osCode the
// packed scalar.
function mkIoError(tag: number, fname: string | null, code: number, details: string): Ctor {
  const named =
    tag === IO_ERROR_ALREADY_EXISTS ||
    (tag >= IO_ERROR_INTERRUPTED && tag <= IO_ERROR_NO_SUCH_THING)
  const plain = tag === IO_ERROR_INTERRUPTED || tag === IO_ERROR_NO_FILE_OR_DIRECTORY
  const e = !named
    ? lean_ctor(tag, 1, 0, 4, details)
    : plain
      ? lean_ctor(tag, 2, 0, 4, fname ?? "", details)
      : lean_ctor(tag, 2, 0, 4, fname === null ? 0 : lean_ctor(1, 1, 0, 0, fname), details)
  e.sdata?.setUint32(0, code, true)
  return e
}

export function lean_mk_io_error_unsupported_operation(details: string): Ctor {
  return mkIoError(IO_ERROR_UNSUPPORTED_OPERATION, null, 0, details)
}

const UV_ERRORS: Readonly<Record<string, readonly [number, string]>> = {
  E2BIG: [IO_ERROR_RESOURCE_EXHAUSTED, "argument list too long"],
  EACCES: [IO_ERROR_PERMISSION_DENIED, "permission denied"],
  EADDRINUSE: [IO_ERROR_RESOURCE_BUSY, "address already in use"],
  EADDRNOTAVAIL: [IO_ERROR_UNSUPPORTED_OPERATION, "address not available"],
  EAFNOSUPPORT: [IO_ERROR_UNSUPPORTED_OPERATION, "address family not supported"],
  EAGAIN: [IO_ERROR_RESOURCE_EXHAUSTED, "resource temporarily unavailable"],
  EBADF: [IO_ERROR_INVALID_ARGUMENT, "bad file descriptor"],
  EBUSY: [IO_ERROR_RESOURCE_BUSY, "resource busy or locked"],
  ECONNABORTED: [IO_ERROR_PERMISSION_DENIED, "software caused connection abort"],
  ECONNREFUSED: [IO_ERROR_NO_SUCH_THING, "connection refused"],
  ECONNRESET: [IO_ERROR_RESOURCE_VANISHED, "connection reset by peer"],
  EDESTADDRREQ: [IO_ERROR_INVALID_ARGUMENT, "destination address required"],
  EEXIST: [IO_ERROR_ALREADY_EXISTS, "file already exists"],
  EFAULT: [IO_ERROR_OTHER, "bad address in system call argument"],
  EFBIG: [IO_ERROR_PERMISSION_DENIED, "file too large"],
  EHOSTUNREACH: [IO_ERROR_NO_SUCH_THING, "host is unreachable"],
  EILSEQ: [IO_ERROR_INVALID_ARGUMENT, "illegal byte sequence"],
  EINTR: [IO_ERROR_INTERRUPTED, "interrupted system call"],
  EINVAL: [IO_ERROR_INVALID_ARGUMENT, "invalid argument"],
  EIO: [IO_ERROR_HARDWARE_FAULT, "i/o error"],
  EISCONN: [IO_ERROR_ALREADY_EXISTS, "socket is already connected"],
  EISDIR: [IO_ERROR_INAPPROPRIATE_TYPE, "illegal operation on a directory"],
  ELOOP: [IO_ERROR_INVALID_ARGUMENT, "too many symbolic links encountered"],
  EMFILE: [IO_ERROR_RESOURCE_EXHAUSTED, "too many open files"],
  EMLINK: [IO_ERROR_RESOURCE_EXHAUSTED, "too many links"],
  EMSGSIZE: [IO_ERROR_RESOURCE_EXHAUSTED, "message too long"],
  ENAMETOOLONG: [IO_ERROR_INVALID_ARGUMENT, "name too long"],
  ENETDOWN: [IO_ERROR_RESOURCE_VANISHED, "network is down"],
  ENETUNREACH: [IO_ERROR_NO_SUCH_THING, "network is unreachable"],
  ENFILE: [IO_ERROR_RESOURCE_EXHAUSTED, "file table overflow"],
  ENOBUFS: [IO_ERROR_RESOURCE_EXHAUSTED, "no buffer space available"],
  ENODEV: [IO_ERROR_UNSUPPORTED_OPERATION, "no such device"],
  ENOENT: [IO_ERROR_NO_FILE_OR_DIRECTORY, "no such file or directory"],
  ENOMEM: [IO_ERROR_RESOURCE_EXHAUSTED, "not enough memory"],
  ENOPROTOOPT: [IO_ERROR_UNSUPPORTED_OPERATION, "protocol not available"],
  ENOSPC: [IO_ERROR_RESOURCE_EXHAUSTED, "no space left on device"],
  ENOSYS: [IO_ERROR_UNSUPPORTED_OPERATION, "function not implemented"],
  ENOTCONN: [IO_ERROR_INVALID_ARGUMENT, "socket is not connected"],
  ENOTDIR: [IO_ERROR_INAPPROPRIATE_TYPE, "not a directory"],
  ENOTEMPTY: [IO_ERROR_UNSATISFIED_CONSTRAINTS, "directory not empty"],
  ENOTSOCK: [IO_ERROR_INVALID_ARGUMENT, "socket operation on non-socket"],
  ENOTTY: [IO_ERROR_ILLEGAL_OPERATION, "inappropriate ioctl for device"],
  ENXIO: [IO_ERROR_NO_SUCH_THING, "no such device or address"],
  EOPNOTSUPP: [IO_ERROR_UNSUPPORTED_OPERATION, "operation not supported on socket"],
  EPERM: [IO_ERROR_PERMISSION_DENIED, "operation not permitted"],
  EPIPE: [IO_ERROR_RESOURCE_VANISHED, "broken pipe"],
  EPROTO: [IO_ERROR_PROTOCOL, "protocol error"],
  EPROTONOSUPPORT: [IO_ERROR_PROTOCOL, "protocol not supported"],
  EPROTOTYPE: [IO_ERROR_PROTOCOL, "protocol wrong type for socket"],
  ERANGE: [IO_ERROR_UNSUPPORTED_OPERATION, "result too large"],
  EROFS: [IO_ERROR_PERMISSION_DENIED, "read-only file system"],
  ESPIPE: [IO_ERROR_UNSUPPORTED_OPERATION, "invalid seek"],
  ESRCH: [IO_ERROR_NO_SUCH_THING, "no such process"],
  ETIMEDOUT: [IO_ERROR_TIME_EXPIRED, "connection timed out"],
  ETXTBSY: [IO_ERROR_RESOURCE_BUSY, "text file is busy"],
  EXDEV: [IO_ERROR_UNSUPPORTED_OPERATION, "cross-device link not permitted"],
  ENODATA: [IO_ERROR_NO_SUCH_THING, "no data available"],
}

function systemError(e: unknown): { readonly code: string; readonly errno: number } | null {
  if (!(e instanceof Error)) return null
  const code: unknown = Reflect.get(e, "code")
  const errno: unknown = Reflect.get(e, "errno")
  return typeof code === "string" && typeof errno === "number" ? { code, errno } : null
}

function ioErrorOf(e: unknown, fname: string | null): Ctor {
  if (e instanceof Error && e.name === "UnsupportedOperation")
    return lean_mk_io_error_unsupported_operation(e.message)
  const sys = systemError(e)
  if (sys !== null) {
    const [tag, details] = UV_ERRORS[sys.code] ?? [
      IO_ERROR_OTHER,
      `Unknown system error ${sys.errno}`,
    ]
    return mkIoError(tag, fname, -sys.errno, details)
  }
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
// gist (and of `details` when present). The osCode is the packed UInt32 scalar;
// the details string is the last object field.
function decap(t: string): string {
  return t.length === 0 ? t : t.charAt(0).toLowerCase() + t.slice(1)
}

function osCode(e: Obj): number {
  const data = asCtor(e).sdata
  if (data === null) throw new TypeError("lean-ts runtime: IO.Error without an osCode")
  return data.getUint32(0, true)
}

function detailsOf(e: Obj): string {
  const fields = asCtor(e).fields
  return asString(fields[fields.length - 1])
}

// `Option String` field: none == 0 (number), some == {tag:1,fields:[s]}.
function optFn(e: Obj): string | null {
  const o = asCtor(e).fields[0]
  return lean_tag(o) === 0 ? null : asString(asCtor(o).fields[0])
}

function ioDetails(code: number, d: string | null): string {
  return " (error code: " + String(code) + (d !== null ? ", " + decap(d) : "") + ")"
}

function ioFopen(gist: string, fn: string, code: number, d: string | null): string {
  return decap(gist) + ioDetails(code, d) + "\n  file: " + fn
}

function ioOther(gist: string, code: number, d: string | null): string {
  return decap(gist) + ioDetails(code, d)
}

function withFile(gist: string, e: Obj): string {
  const fn = optFn(e)
  return fn !== null
    ? ioFopen(gist, fn, osCode(e), detailsOf(e))
    : ioOther(gist, osCode(e), detailsOf(e))
}

export function lean_io_error_to_string(e: Obj): string {
  switch (lean_tag(e)) {
    case IO_ERROR_ALREADY_EXISTS:
      return withFile("already exists", e)
    case IO_ERROR_OTHER:
      return ioOther(detailsOf(e), osCode(e), null)
    case IO_ERROR_RESOURCE_BUSY:
      return ioOther("resource busy", osCode(e), detailsOf(e))
    case IO_ERROR_RESOURCE_VANISHED:
      return ioOther("resource vanished", osCode(e), detailsOf(e))
    case IO_ERROR_UNSUPPORTED_OPERATION:
      return ioOther("unsupported operation", osCode(e), detailsOf(e))
    case IO_ERROR_HARDWARE_FAULT:
      return ioOther("hardware fault", osCode(e), null)
    case IO_ERROR_UNSATISFIED_CONSTRAINTS:
      return ioOther("directory not empty", osCode(e), null)
    case IO_ERROR_ILLEGAL_OPERATION:
      return ioOther("illegal operation", osCode(e), detailsOf(e))
    case IO_ERROR_PROTOCOL:
      return ioOther("protocol error", osCode(e), detailsOf(e))
    case IO_ERROR_TIME_EXPIRED:
      return ioOther("time expired", osCode(e), detailsOf(e))
    case IO_ERROR_INTERRUPTED:
      return ioFopen(
        "interrupted system call",
        asString(asCtor(e).fields[0]),
        osCode(e),
        detailsOf(e),
      )
    case IO_ERROR_NO_FILE_OR_DIRECTORY:
      return ioFopen("no such file or directory", asString(asCtor(e).fields[0]), osCode(e), null)
    case IO_ERROR_INVALID_ARGUMENT:
      return withFile("invalid argument", e)
    case IO_ERROR_PERMISSION_DENIED: {
      const fn = optFn(e)
      return fn !== null
        ? ioFopen(detailsOf(e), fn, osCode(e), null)
        : ioOther(detailsOf(e), osCode(e), null)
    }
    case IO_ERROR_RESOURCE_EXHAUSTED:
      return withFile("resource exhausted", e)
    case IO_ERROR_INAPPROPRIATE_TYPE:
      return withFile("inappropriate type", e)
    case IO_ERROR_NO_SUCH_THING:
      return withFile("no such thing", e)
    case 17:
      return "end of file"
    case IO_ERROR_USER:
      return asString(asCtor(e).fields[0])
    default:
      throw new TypeError(`lean-ts runtime: IO.Error has no constructor ${lean_tag(e)}`)
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

function ioAction(act: () => Obj, fname: string | null = null): Ctor {
  try {
    return lean_io_result_mk_ok(act())
  } catch (e) {
    return lean_io_result_mk_error(ioErrorOf(e, fname))
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
  const p = asString(path)
  return ioAction(() => ({ fd: platform.openFile(p, MODE_FLAG[mode] ?? "r") }), p)
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
