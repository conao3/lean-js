import LeanTs

open Lean LeanTs

def version : String := "0.1.0"

/-- Version of the generated code. Raise it when the emitted code changes, together with
    `GENERATOR_VERSION` of `src/embed.ts`; `lean-ts sync` checks it and puts it into its keys. -/
def generatorVersion : String := "4"

def usage : String := "usage: lean-typescript [--version] [--generator-version] <command> <subcommand> [parameters]

commands:
  module generate      Emit a TypeScript module for functions of a Lean module
  project generate     Build a lake project and emit a TypeScript module per Lean module
  obligations check    Judge the proofs of obligations (used by `lean-ts check`)

lean-typescript module generate
  --module-name <Name>        Lean module to import (required unless --batch)
  --roots <Name> ...          Functions to export (default: the module's public definitions)
  --main <Name>               Also emit the program entry running <Name> as `main`
                              (after the module's init decls)
  --namespace <Name>          Namespace removed from the public TypeScript names (default: the module name)
  --type-module <Name>=<specifier> ...
                              Types in namespace <Name> are exports of the TypeScript module <specifier>
  --model-module <Name>=<key> ...
                              Types in namespace <Name> are the user schemas registered as <key>
  --tag-key <key>             Discriminant key of the inductive types (default: ctor)
  --option null|undefined     TypeScript form of `Option α` (default: null)
  --batch <file>              JSON array of jobs {\"module\", \"output_file\", \"roots\"?, \"namespace\"?,
                              \"type_modules\"?: [{\"namespace\", \"module\"}],
                              \"model_modules\"?: [{\"namespace\", \"key\", \"module\"?, \"export\"?}],
                              \"tag_key\"?, \"option\"?,
                              \"block\"?: {\"name\", \"module\", \"fnv\"}}
                              run against one environment importing all their modules
  --import <Name> ...         More modules to import (their @[csimp] lemmas apply)
  --search-path <dir> ...     Extra .olean search directories
  --output-file <path>        Write the module here (default: standard output)
  --runtime-path <specifier>  Module the generated code imports the runtime from
                              (default: lean-ts/runtime)
  --internal-only             Export the internal functions instead of the public wrappers
  --output json|text          Format of the summary

lean-typescript project generate
  --lake-dir <dir>            Lake project to build (required)
  --output-dir <dir>          Directory of the TypeScript modules, one <A>/<B>.ts per module A.B (required)
  --modules <Name> ...        Modules to emit (default: every module the package builds)
  --runtime-path, --output    as above

lean-typescript obligations check
  --modules <Name> ...        Modules to import (required)
  --obligations <file>        JSON array of {\"model\": <Lean name>, \"label\": <label>} (required)
  --search-path <dir> ...     Extra .olean search directories
  Prints a JSON array of {\"model\", \"label\", \"status\", \"axioms\"?, \"file\"?, \"line\"?}; the
  status is proved, sorry, axioms, missing, mismatch or unextracted

exit codes: 0 success, 252 invalid parameters, 254 input that cannot be converted, 255 other errors
"

structure Opts where
  moduleName : Option Name := none
  roots : Array Name := #[]
  main? : Option Name := none
  searchPath : Array System.FilePath := #[]
  outputFile : Option System.FilePath := none
  runtimePath : String := "lean-ts/runtime"
  internalOnly : Bool := false
  namespace? : Option Name := none
  output : String := "json"
  imports : Array Name := #[]
  typeModules : Array (Name × String) := #[]
  modelModules : Array (Name × String) := #[]
  settings : Settings := {}
  batch : Option System.FilePath := none
  lakeDir : Option System.FilePath := none
  outputDir : Option System.FilePath := none
  modules : Array Name := #[]
  obligations : Option System.FilePath := none

def parseAssoc (s : String) : Except String (Name × String) :=
  match s.splitOn "=" with
  | [ns, m] => if ns.isEmpty || m.isEmpty then .error s!"expected <Name>=<value>: {s}" else .ok (ns.toName, m)
  | _ => .error s!"expected <Name>=<value>: {s}"

partial def parseOpts (args : List String) (o : Opts) : Except String Opts :=
  let takeMany (rest : List String) : List String × List String :=
    (rest.takeWhile (!·.startsWith "--"), rest.dropWhile (!·.startsWith "--"))
  match args with
  | [] => .ok o
  | "--module-name" :: v :: rest => parseOpts rest { o with moduleName := v.toName }
  | "--namespace" :: v :: rest => parseOpts rest { o with namespace? := v.toName }
  | "--main" :: v :: rest => parseOpts rest { o with main? := v.toName }
  | "--output-file" :: v :: rest => parseOpts rest { o with outputFile := some v }
  | "--runtime-path" :: v :: rest => parseOpts rest { o with runtimePath := v }
  | "--internal-only" :: rest => parseOpts rest { o with internalOnly := true }
  | "--tag-key" :: v :: rest => parseOpts rest { o with settings := { o.settings with tagKey := v } }
  | "--option" :: v :: rest => parseOpts rest { o with settings := { o.settings with option := v } }
  | "--batch" :: v :: rest => parseOpts rest { o with batch := some v }
  | "--lake-dir" :: v :: rest => parseOpts rest { o with lakeDir := some v }
  | "--output-dir" :: v :: rest => parseOpts rest { o with outputDir := some v }
  | "--obligations" :: v :: rest => parseOpts rest { o with obligations := some v }
  | "--output" :: v :: rest =>
    if v == "json" || v == "text" then parseOpts rest { o with output := v }
    else .error s!"--output must be json or text: {v}"
  | "--roots" :: rest =>
    let (vs, rest) := takeMany rest
    parseOpts rest { o with roots := o.roots ++ vs.toArray.map String.toName }
  | "--modules" :: rest =>
    let (vs, rest) := takeMany rest
    parseOpts rest { o with modules := o.modules ++ vs.toArray.map String.toName }
  | "--import" :: rest =>
    let (vs, rest) := takeMany rest
    parseOpts rest { o with imports := o.imports ++ vs.toArray.map String.toName }
  | "--search-path" :: rest =>
    let (vs, rest) := takeMany rest
    parseOpts rest { o with searchPath := o.searchPath ++ vs.toArray.map System.FilePath.mk }
  | "--type-module" :: rest =>
    let (vs, rest) := takeMany rest
    match vs.mapM parseAssoc with
    | .ok ps => parseOpts rest { o with typeModules := o.typeModules ++ ps.toArray }
    | .error e => .error s!"--type-module: {e}"
  | "--model-module" :: rest =>
    let (vs, rest) := takeMany rest
    match vs.mapM parseAssoc with
    | .ok ps => parseOpts rest { o with modelModules := o.modelModules ++ ps.toArray }
    | .error e => .error s!"--model-module: {e}"
  | a :: _ => .error s!"unknown parameter: {a}"

def fail (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln s!"lean-typescript: {msg}"
  return code

structure BlockInfo where
  name : String
  module : String
  fnv : String

structure Job where
  module : Name
  roots : Array Name := #[]
  main? : Option Name := none
  namespace? : Option Name := none
  outputFile : Option System.FilePath := none
  typeModules : Array (Name × String) := #[]
  modelModules : Array ModelRef := #[]
  settings : Settings := {}
  block? : Option BlockInfo := none

/-- The definitions of `mod` exported by default: public, written in the source (with a declaration
    range), not instances or their auxiliary definitions, with IR. -/
def defaultRoots (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut out := #[]
  for c in env.header.moduleData[idx.toNat]!.constNames do
    if isPrivateName c || c.isInternalDetail || isAuxRecursor env c then continue
    if Meta.isInstanceCore env c || Meta.isInstanceCore env c.getPrefix then continue
    if (declRangeExt.find? (level := .exported) env c).isNone then continue
    if (IR.findEnvDecl env c).isSome then out := out.push c
  return out

def moduleTypes (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut out := #[]
  for c in env.header.moduleData[idx.toNat]!.constNames do
    if isPrivateName c || c.isInternalDetail then continue
    let some (.inductInfo ind) := env.find? c | continue
    if ind.numParams != 0 || ind.numIndices != 0 || ind.isUnsafe || isClass env c then continue
    if ind.type.isProp then continue
    if (declRangeExt.find? (level := .exported) env c).isNone then continue
    out := out.push c
  return out

def header (o : Opts) (mod : Name) (imports body : String) : String :=
  let types := if (body.splitOn "Obj").length > 1 then s!"import type \{ Obj } from \"{o.runtimePath}\"\n" else ""
  s!"// Generated by lean-typescript (generator {generatorVersion}) from {mod}. Do not edit.\nimport * as L from \"{o.runtimePath}\"\n{types}{imports}\n"

def registration (b : BlockInfo) (s : Settings) : String :=
  s!"L.registerBlock(\{ name: {quoteString b.name}, module: {quoteString b.module}, fnv: {quoteString b.fnv}, settings: \{ tagKey: {quoteString s.tagKey}, option: {quoteString s.option} }, url: import.meta.url })\n\n"

def importAll (o : Opts) (mods : Array Name) : IO (Except Name Environment) := do
  initSearchPath (← findSysroot) o.searchPath.toList
  let sp ← searchPathRef.get
  for m in mods do
    if (← sp.findWithExt "olean" m).isNone then return .error m
  .ok <$> importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024) (loadExts := true)

def printSummary (o : Opts) (toStderr : Bool) (j : Json) : IO Unit := do
  let out := if toStderr then IO.eprintln else IO.println
  let get (k : String) := j.getObjValD k
  let mod := (get "module").getStr?.toOption.getD ""
  match (get "error").getStr? with
  | .ok e => IO.eprintln s!"lean-typescript: {mod}: {e}"
  | .error _ =>
    if o.output == "json" then out j.compress
    else
      let size (k : String) := (get k).getArr?.toOption.getD #[] |>.size
      out s!"{mod}: {get "functions"} functions, {size "externs"} externs, {size "public"} public, {size "types"} types"
      for s in (get "skipped").getArr?.toOption.getD #[] do
        IO.eprintln s!"lean-typescript: skipped {(s.getObjValD "name").getStr?.toOption.getD ""}: {(s.getObjValD "reason").getStr?.toOption.getD ""}"

def collect (env : Environment) (cfg : MarshalCfg) (types roots : Array Name) :
    IO (Collected × Environment) := do
  let ctx : Core.Context := { fileName := "<lean-typescript>", fileMap := default, maxHeartbeats := 0 }
  let ((r, _), st) ← ((((collectPublics types roots).run {}).run cfg).run').toIO ctx { env }
  return (r, st.env)

def runJob (env : Environment) (o : Opts) (job : Job) : IO (Json × UInt32) := do
  let failed (code : UInt32) (msg : String) : IO (Json × UInt32) :=
    return (Json.mkObj [("module", toString job.module), ("error", msg), ("code", code.toNat)], code)
  if env.getModuleIdx? job.module |>.isNone then return ← failed 252 s!"module not imported: {job.module}"
  if let .error e := job.settings.check then return ← failed 254 e
  let defaults := job.roots.isEmpty && job.main?.isNone
  let roots := if defaults then defaultRoots env job.module else job.roots
  let cfg : MarshalCfg := { strip := job.namespace?.getD job.module, typeModules := job.typeModules,
                            modelModules := job.modelModules, settings := job.settings }
  let (col, env) ← if o.internalOnly then pure ({ publics := #[], skipped := #[], state := {} }, env)
    else collect env cfg (if defaults then moduleTypes env job.module else #[]) roots
  unless col.fatal.isEmpty do return ← failed 254 ("; ".intercalate col.fatal.toList)
  let internalRoots := if o.internalOnly then roots else col.publics.map (·.lean) ++ col.state.deciders
  match renderModule env internalRoots job.main? (exportRoots := o.internalOnly) with
  | .error e => failed 254 e
  | .ok r =>
    let missing := r.externs.filter (!runtimeExterns.contains ·)
    unless missing.isEmpty do
      return ← failed 254 s!"externs not in the runtime: {", ".intercalate missing.toList}"
    let pub ← match renderPublic env job.settings col.publics col.state with
      | .ok p => pure p
      | .error e => return ← failed 254 e
    let body := if pub.body.isEmpty then r.body else r.body ++ "\n" ++ pub.body
    let reg := job.block?.map (registration · job.settings) |>.getD ""
    let src := header o job.module pub.imports (reg ++ body) ++ reg ++ body
    match job.outputFile with
    | none => IO.print src
    | some p =>
      if let some dir := p.parent then IO.FS.createDirAll dir
      IO.FS.writeFile p src
    let publicJson := col.publics.map fun f => Json.mkObj [("lean", toString f.lean), ("typescript", f.dotted)]
    let typesJson := pub.types.map fun t => Json.mkObj [("lean", toString t.lean), ("typescript", t.ident)]
    let skippedJson := col.skipped.map fun s => Json.mkObj [("name", toString s.name), ("reason", s.reason)]
    return (Json.mkObj [("module", toString job.module), ("functions", r.functions),
      ("externs", Json.arr (r.externs.map Json.str)), ("public", Json.arr publicJson),
      ("types", Json.arr typesJson), ("skipped", Json.arr skippedJson)], 0)

def runJobs (o : Opts) (jobs : Array Job) : IO (Array Json × UInt32) := do
  let mods := (jobs.map (·.module) ++ o.imports).foldl (fun a m => if a.contains m then a else a.push m) #[]
  let env ← match ← importAll o mods with
    | .ok env => pure env
    | .error m =>
      let j := Json.mkObj [("module", toString m), ("error", s!"module not found: {m}"), ("code", 252)]
      return (#[j], 252)
  let mut out := #[]
  let mut code : UInt32 := 0
  for job in jobs do
    let (j, c) ← runJob env o job
    out := out.push j
    if c != 0 && code == 0 then code := c
  return (out, code)

def parseAssocs (e : Json) (field key : String) : Except String (Array (Name × String)) := do
  let arr := (e.getObjValAs? (Array Json) field).toOption.getD #[]
  arr.mapM fun t => do
    let ns ← t.getObjValAs? String "namespace"
    let v ← t.getObjValAs? String key
    pure (ns.toName, v)

def parseModels (e : Json) : Except String (Array ModelRef) := do
  let arr := (e.getObjValAs? (Array Json) "model_modules").toOption.getD #[]
  arr.mapM fun t => do
    let ns ← t.getObjValAs? String "namespace"
    let key ← t.getObjValAs? String "key"
    let module := (t.getObjValAs? String "module").toOption.getD ""
    let exportName := (t.getObjValAs? String "export").toOption.getD ""
    pure { ns := ns.toName, key, module, exportName }

def parseJobs (defaults : Settings) (j : Json) : Except String (Array Job) := do
  let arr ← j.getArr?
  arr.mapM fun e => do
    let module := (← e.getObjValAs? String "module").toName
    let outputFile := some (System.FilePath.mk (← e.getObjValAs? String "output_file"))
    let roots := (e.getObjValAs? (Array String) "roots").toOption.getD #[] |>.map String.toName
    let namespace? := (e.getObjValAs? String "namespace").toOption.map String.toName
    let typeModules ← parseAssocs e "type_modules" "module"
    let modelModules ← parseModels e
    let settings : Settings := { tagKey := (e.getObjValAs? String "tag_key").toOption.getD defaults.tagKey,
                                 option := (e.getObjValAs? String "option").toOption.getD defaults.option }
    let block? ← match e.getObjVal? "block" with
      | .error _ => pure none
      | .ok b => pure (some { name := ← b.getObjValAs? String "name", module := ← b.getObjValAs? String "module",
                              fnv := ← b.getObjValAs? String "fnv" })
    return { module, outputFile, roots, namespace?, typeModules, modelModules, settings, block? }

def moduleGenerate (o : Opts) : IO UInt32 := do
  if let .error e := o.settings.check then return ← fail 254 s!"--tag-key/--option: {e}"
  if let some file := o.batch then
    let jobs ← match Json.parse (← IO.FS.readFile file) >>= parseJobs o.settings with
      | .ok js => pure js
      | .error e => return ← fail 252 s!"invalid --batch file {file}: {e}"
    let (out, code) ← runJobs o jobs
    if o.output == "json" then IO.println (Json.arr out).compress
    else for j in out do printSummary o false j
    return code
  let some mod := o.moduleName | return ← fail 252 "--module-name is required"
  let job : Job := { module := mod, roots := o.roots, main? := o.main?, namespace? := o.namespace?,
                     outputFile := o.outputFile, typeModules := o.typeModules,
                     modelModules := o.modelModules.map fun (ns, key) => { ns, key },
                     settings := o.settings }
  let (out, code) ← runJobs o #[job]
  for j in out do printSummary o o.outputFile.isNone j
  return code

def runCmd (cmd : String) (args : Array String) (cwd : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd, args, cwd }
  if out.exitCode != 0 then
    throw (IO.userError s!"{cmd} {" ".intercalate args.toList} failed ({out.exitCode}):\n{out.stdout}{out.stderr}")
  return out.stdout

partial def oleanModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← oleanModules e.path (pre.str e.fileName))
    else if e.fileName.endsWith ".olean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

def modulePath (outDir : System.FilePath) (m : Name) : System.FilePath :=
  (m.components.foldl (fun p c => p / componentString c) outDir).addExtension "ts"

def projectGenerate (o : Opts) : IO UInt32 := do
  let some lakeDir := o.lakeDir | return ← fail 252 "--lake-dir is required"
  let some outDir := o.outputDir | return ← fail 252 "--output-dir is required"
  unless ← lakeDir.isDir do return ← fail 252 s!"not a directory: {lakeDir}"
  let lake := (← IO.getEnv "LAKE").getD "lake"
  discard <| runCmd lake (#["build"] ++ o.modules.map toString) lakeDir
  let leanPath := (← runCmd lake #["env", "printenv", "LEAN_PATH"] lakeDir).trimAscii.toString
  let paths := (leanPath.splitOn ":").filter (!·.isEmpty) |>.toArray.map System.FilePath.mk
  let lib := lakeDir / ".lake" / "build" / "lib" / "lean"
  let mods ← if o.modules.isEmpty then oleanModules lib .anonymous else pure o.modules
  let mods := mods.qsort (·.toString < ·.toString)
  if mods.isEmpty then return ← fail 252 s!"no modules in {lakeDir}"
  let jobs := mods.map fun m => { module := m, outputFile := some (modulePath outDir m) : Job }
  let (out, code) ← runJobs { o with searchPath := o.searchPath ++ paths } jobs
  if o.output == "json" then IO.println (Json.arr out).compress
  else for j in out do printSummary o false j
  return code

def obligationsCheck (o : Opts) : IO UInt32 := do
  let some file := o.obligations | return ← fail 252 "--obligations is required"
  if o.modules.isEmpty then return ← fail 252 "--modules is required"
  let obls ← match Json.parse (← IO.FS.readFile file) >>= parseObligations with
    | .ok v => pure v
    | .error e => return ← fail 252 s!"invalid --obligations file {file}: {e}"
  match ← importAll o o.modules with
  | .error m => fail 252 s!"no .olean for {m} in the search path"
  | .ok env =>
    let ctx : Core.Context := { fileName := "<lean-typescript>", fileMap := default, maxHeartbeats := 0 }
    let (out, _) ← ((obls.mapM checkObligation).run').toIO ctx { env }
    IO.println (Json.arr out).compress
    return 0

def withOpts (rest : List String) (k : Opts → IO UInt32) : IO UInt32 :=
  match parseOpts rest {} with
  | .error e => fail 252 e
  | .ok o =>
    try k o
    catch e => fail 255 (toString e)

unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  match args with
  | ["--version"] => IO.println version; return 0
  | ["--generator-version"] => IO.println generatorVersion; return 0
  | [] | ["help"] | ["--help"] => IO.print usage; return 0
  | "module" :: "help" :: _ | "project" :: "help" :: _ => IO.print usage; return 0
  | "module" :: "generate" :: rest => withOpts rest moduleGenerate
  | "project" :: "generate" :: rest => withOpts rest projectGenerate
  | "obligations" :: "check" :: rest => withOpts rest obligationsCheck
  | _ => fail 252 s!"unknown command (see `lean-typescript help`)"
