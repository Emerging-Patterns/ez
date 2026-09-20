# pkg/pkg: the package a `bend <entry> --publish` would upload, computed
# without publishing: the file set, their sha256s, and the `0x<hash>` that names
# them. This mirrors `pkg_files` and the hash in bend's `cli_publish`.
# `tests/publish.sh` pins it against the real thing by running `bend --publish`
# at a local hub, so drift fails the gate rather than the ecosystem.
import Base
import ../io/file.bend as F
import ../run/run.bend as R
import ../sha/sha.bend as Sha
import ./path.bend as P

# a file of a package: the path it takes inside the package, and its sha256
type File is Data:
  File{at: String, sum: String}

# a package: the files it holds, the hash that names them, and the directory
# their paths are written from. The root is the entry's own directory until a
# module reached through `..` re-roots the package above it, so a caller
# copying the files out joins them against this and never against the entry's
# directory.
type Pkg is Data:
  Pkg{hash: String, root: String, files: List<&2, File>}

# what a source file's header imports: modules by the path they were reached
# through, and the foreign C and JS bodies bend uploads alongside the sources
type Scan is Data:
  Scan{mods: List<&2, String>, foreign: List<&2, String>}

# what one line of a source file turned out to be
type Stmt is Data:
  SNone{}
  SMod{spec: String}
  SForeign{at: String}
  SBody{}

# a scan in progress: `head` is true while the imports still head the file
type Head is Data:
  Head{head: Bool, mods: List<&2, String>, foreign: List<&2, String>}

# the words of a line, with the runs of spaces dropped
def words.keep(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case []:
      []
    case Con{+h, t}:
      +more = words.keep(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# the words of a line
def words(s: String) -> List<&2, String>:
  words.keep(String.split(s, ' '))

# the nth word, or "" when the line is shorter than that. Both the list and the
# count are scrutinised together, so the walk needs no helper to branch through.
def word(ws: List<&2, String>, n: Nat) -> String:
  match ws n:
    case Nil{} _m:
      ""
    case Con{h, _t} 0n:
      h
    case Con{_h, t} 1n+p:
      word(t, p)

# the line named a module, or it did not, with the answer already in hand.
# `Bool.pick` is an ordinary function and builds both of its arms before it
# picks one, so under it `word(ws, 1n)` walked the words of every line of
# every source file ez scans. An arm of a `match` is not built until it is
# taken.
def mod_of.step(named: Bool, ws: List<&2, String>) -> Stmt:
  match named:
    case True{}:
      SMod{word(ws, 1n)}
    case False{}:
      SBody{}

# an `import <spec> as <Name>` line names a module; anything else does not
def mod_of(+ws: List<&2, String>) -> Stmt:
  mod_of.step(
    Bool.and(Nat.is_ge(List.length(&2, String, ws), 4n),
      Bool.and(String.eq(word(ws, 0n), "import"), String.eq(word(ws, 2n), "as"))),
    ws)

# the prelude decided. The prelude arm does no work at all, and the other arm
# is the only place `mod_of` has anything to say, so this is where the rest of
# the classification hangs rather than in an argument that always runs.
def base_of.step(prelude: Bool, ws: List<&2, String>) -> Stmt:
  match prelude:
    case True{}:
      SNone{}
    case False{}:
      mod_of(ws)

# `import Base` brings in the prelude, which is no part of any package
def base_of(+ws: List<&2, String>) -> Stmt:
  base_of.step(
    Bool.and(Nat.is_eq(List.length(&2, String, ws), 2n),
      Bool.and(String.eq(word(ws, 0n), "import"), String.eq(word(ws, 1n), "Base"))),
    ws)

# a line that neither opens nor ends the header
def quiet(+s: String) -> Bool:
  Bool.or(String.is_empty(s), String.starts_with(s, "#"))

# a line that says nothing about the header, decided. `words` is a
# `String.split` and a filter over its result, and this is the arm it hangs
# from: every blank line and every comment line of every `.bend` file of the
# project and of every package it resolves used to be split into words and
# classified, which is most of the lines ez ever reads.
def stmt_of.quiet(skip: Bool, +s: String) -> Stmt:
  match skip:
    case True{}:
      SNone{}
    case False{}:
      base_of(words(s))

# the foreign import decided. The rest of the cascade hangs off the False arm
# rather than sitting in an argument, so a line that is a foreign import pays
# for nothing below it.
def stmt_of.foreign(here: Bool, +s: String) -> Stmt:
  match here:
    case True{}:
      SForeign{String.take(String.drop(s, 8n), Nat.sub(String.length(s), 9n))}
    case False{}:
      stmt_of.quiet(quiet(s), s)

# a trimmed line classified. A foreign import is tested first: it lives in a
# def's body, long after the header has ended.
def stmt_of(+s: String) -> Stmt:
  stmt_of.foreign(
    Bool.and(String.starts_with(s, "import \""), String.ends_with(s, "\"")), s)

# a module named after the header has ended is not part of the header, so the
# line is ignored rather than followed
def scan.mod(+head: Bool, spec: String, mods: List<&2, String>,
  foreign: List<&2, String>) -> Head:
  match head:
    case True{}:
      Head{True{}, spec <> mods, foreign}
    case False{}:
      Head{False{}, mods, foreign}

# the state once a line has been classified
def scan.go(st: Head, s: Stmt) -> Head:
  Head{head, mods, foreign} = st
  match s:
    case SNone{}:
      Head{head, mods, foreign}
    case SForeign{at}:
      Head{head, mods, at <> foreign}
    case SMod{spec}:
      scan.mod(head, spec, mods, foreign)
    case SBody{}:
      Head{False{}, mods, foreign}

# one line of a source file against the state
def scan.step(st: Head, raw: String) -> Head:
  scan.go(st, stmt_of(String.trim(raw)))

# what a finished scan gathered, in source order
def scan.fin(st: Head) -> Scan:
  Head{_head, mods, foreign} = st
  Scan{List.reverse(&2, String, mods), List.reverse(&2, String, foreign)}

# the header walked one line at a time. Base's `List.foldl` applies an erased
# function parameter, which Bend's termination check cannot see through, so
# every def reaching it is reported as relying on unsafe code; a walk written
# out is structural and costs nothing.
def scan.walk(ls: List<&2, String>, st: Head) -> Head:
  match ls:
    case []:
      st
    case h <> t:
      scan.walk(t, scan.step(st, h))

# what a source file's header imports
def scan(text: String) -> Scan:
  scan.fin(scan.walk(String.lines(text), Head{True{}, [], []}))

# the modules a scan found
def scan.mods(s: Scan) -> List<&2, String>:
  Scan{mods, _foreign} = s
  mods

# the foreign bodies a scan found
def scan.foreign(s: Scan) -> List<&2, String>:
  Scan{_mods, foreign} = s
  foreign

# an import of a hub package, which is a dependency rather than a module of
# this package. A `0x` name has no directory of its own, so the first `/` ends
# it.
def is_hub(+spec: String) -> Bool:
  Bool.and(String.starts_with(spec, "0x"), String.contains(spec, "/"))

# a file to visit: where it is on disk, and the module name bend gives it,
# which is the path it was reached through with the `.bend` dropped
type Task is Data:
  Task{file: String, ns: String}

# a file of the package as it was found: where it sits inside the package, and
# its sha256
type Found is Data:
  Found{raw: String, sum: String}

# the walk so far: the files already visited, and what was found
type State is Data:
  State{seen: List<&2, String>, out: List<&2, Found>}

# what one file of the walk answered: the walk so far, and the modules it asks
# for next
type Step is Data:
  Step{st: State, kids: List<&2, Task>}

# a foreign body, named the way the module importing it is named: from that
# module's own directory. `bend --publish` writes `src/util/beep.c` for a body
# imported by `src/util/math.bend`, so anything flatter is a different package
# from the one bend would upload.
def foreign.put(m: Maybe<&2, String>, raw: String) -> List<&2, Found>:
  match m:
    case None{}:
      []
    case Some{src}:
      [Found{raw, Sha.hex(src)}]

# one foreign body, or nothing when it is not on disk. bend uploads only the
# ones that are there.
def foreign_of(+d: String, nd: String, +at: String) -> IO(List<&2, Found>):
  do IO<List<&2, Found>>:
    m : Maybe<&2, String> <- F.read(P.join(d, at))
    return foreign.put(m, P.join(nd, at))

# every foreign body a file imports
def foreigns(+d: String, +nd: String, ats: List<&2, String>) -> IO(List<&2, Found>):
  match ats:
    case []:
      IO.pure(List<&2, Found>, [])
    case h <> t:
      do IO<List<&2, Found>>:
        rest : List<&2, Found> <- foreigns(d, nd, t)
        one : List<&2, Found> <- foreign_of(d, nd, h)
        return List.append(&2, Found, one, rest)

# a module import as the file to visit next, or nothing when it names a hub
# package
def task_of(+d: String, +nd: String, +spec: String) -> List<&2, Task>:
  Bool.pick(List<&2, Task>, is_hub(spec), [],
    [Task{P.join(d, spec), P.unbend(P.join(nd, spec))}])

# every module a file imports, as the files to visit next
def tasks(+d: String, +nd: String, ms: List<&2, String>) -> List<&2, Task>:
  match ms:
    case []:
      []
    case h <> t:
      List.append(&2, Task, task_of(d, nd, h), tasks(d, nd, t))

# the directory a module's own imports are named from. The entry is the package
# root, so its modules are named from nowhere in particular.
def nsdir(+ns: String) -> String:
  Bool.pick(String, String.is_empty(ns), "", P.dir(ns))

# the entry file is written under its own base name; every other module under
# the path it was reached through
def raw_of(+ns: String, eb: String) -> String:
  Bool.pick(String, String.is_empty(ns), eb, ns ++ ".bend")

# a file that was read: itself, its foreign bodies, and the modules it imports
def visit.found(sc: Scan, sum: String, +file: String, +ns: String, eb: String,
  seen: List<&2, String>, out: List<&2, Found>) -> IO(Step):
  Scan{mods, foreign} = sc
  +d = P.dir(file)
  +nd = nsdir(ns)
  do IO<Step>:
    fs : List<&2, Found> <- foreigns(d, nd, foreign)
    return Step{
      State{file <> seen, Found{raw_of(ns, eb), sum} <> List.append(&2, Found, fs, out)},
      tasks(d, nd, mods)}

# a module that is imported but not on disk stops the walk, since a package
# missing a file is not the package bend would publish
def visit.have(m: Maybe<&2, String>, +file: String, ns: String, eb: String,
  seen: List<&2, String>, out: List<&2, Found>) -> IO(Step):
  match m:
    case None{}:
      IO.die(Step, 1, "ez: " ++ file ++ " is imported but not there")
    case Some{+src}:
      visit.found(scan(src), Sha.hex(src), file, ns, eb, seen, out)

# a file not visited before, read and taken apart
def visit.read(+file: String, ns: String, eb: String, seen: List<&2, String>,
  out: List<&2, Found>) -> IO(Step):
  do IO<Step>:
    m : Maybe<&2, String> <- F.read(file)
    visit.have(m, file, ns, eb, seen, out)

# a file already visited keeps the name it was first reached through, the way
# bend's own walk does
def visit.go(hit: Bool, file: String, ns: String, eb: String,
  seen: List<&2, String>, out: List<&2, Found>) -> IO(Step):
  match hit:
    case True{}:
      IO.pure(Step, Step{State{seen, out}, []})
    case False{}:
      visit.read(file, ns, eb, seen, out)

# one step of the scan, with the head's answer in hand. `Bool.or` is an
# ordinary function and so reduces both of its sides, which means a scan
# written with it never stops at the name it was looking for. The rest of the
# scan arrives as a thunk and only the arm that wants it applies it. This list
# grows by one with every file the walk reaches, so the scan is the inner half
# of a quadratic and stopping early halves it.
def seen.has.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a name is already among the ones the walk has reached. Base's
# `List.contains` applies an erased equality, which falls outside the
# termination check; this scan is structural.
def seen.has(xs: List<&2, String>, +s: String) -> Bool:
  match xs:
    case []:
      False{}
    case +h <> t:
      seen.has.step(String.eq(h, s), _u => seen.has(t, s))

# one file of the walk: what it adds to the package, and what it asks for next
def visit(eb: String, tk: Task, st: State) -> IO(Step):
  Task{+file, ns} = tk
  State{+seen, out} = st
  visit.go(seen.has(seen, file), file, ns, eb, seen, out)

# what a visit answered, with its modules put at the front of the queue, so the
# walk goes depth first the way bend's does
def walk.rest(r: Step, rest: List<&2, Task>,
  go: State -> List<&2, Task> -> IO(State)) -> IO(State):
  Step{st, kids} = r
  go(st, List.append(&2, Task, kids, rest))

# the next file of the queue, handed on with what is left of it. An empty queue
# is the end of the walk.
def walk.pop(queue: List<&2, Task>, +st: State,
  go: State -> Task -> List<&2, Task> -> IO(State)) -> IO(State):
  match queue:
    case []:
      IO.pure(State, st)
    case h <> t:
      go(st, h, t)

# one file visited, and the walk carried on. The carrying on arrives as a
# function, since two defs in Bend may not call each other.
def walk.step(+eb: String, h: Task, st: State, rest: List<&2, Task>,
  go: State -> List<&2, Task> -> IO(State)) -> IO(State):
  do IO<State>:
    r : Step <- visit(eb, h, st)
    walk.rest(r, rest, go)

# every file of the package, reached from the entry. The queue is a stack, and
# a file is read once; a path is its own identity, since Base cannot ask the
# file system for a real one.
def walk(fuel: Nat, +eb: String, queue: List<&2, Task>, st: State) -> IO(State):
  match fuel:
    case 0n:
      IO.pure(State, st)
    case 1n+f:
      walk.pop(queue, st, s => h => rest =>
        walk.step(eb, h, s, rest, s2 => q => walk(f, eb, q, s2)))

# the files a walk found
def state.out(st: State) -> List<&2, Found>:
  State{_seen, out} = st
  out

# how far a found file climbs out of the entry's directory
def found.ups(f: Found) -> Nat:
  Found{raw, _sum} = f
  P.ups(raw)

# the deepest climb any file of the package makes
def climb(fs: List<&2, Found>) -> Nat:
  match fs:
    case []:
      0n
    case h <> t:
      Nat.max(found.ups(h), climb(t))

# the entry's own directory, named absolutely. Base cannot ask the file system,
# so `realpath` is asked instead, and only when something actually climbs.
def anc.at(+n: Nat, dir: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["realpath", dir])
    return P.tail(String.trim(R.text(out)), n)

# the trailing components of the entry's directory that the package re-roots
# under: as many as its deepest climb, and none at all when nothing climbs
def anc(n: Nat, dir: String) -> IO(String):
  match n:
    case 0n:
      IO.pure(String, "")
    case 1n+p:
      anc.at(Nat.add(p, 1n), dir)

# a found file, placed under whatever the package re-rooted at
def file_of(+pre: String, f: Found) -> File:
  Found{raw, sum} = f
  File{P.join(pre, raw), sum}

# every found file, placed
def placed(+pre: String, fs: List<&2, Found>) -> List<&2, File>:
  match fs:
    case []:
      []
    case h <> t:
      file_of(pre, h) <> placed(pre, t)

# where a file sits inside its package
def file.at(f: File) -> String:
  File{at, _sum} = f
  at

# a package's files are written in path order, so the manifest of a package is
# the same text whoever computes it
def file.le(a: File, b: File) -> Bool:
  String.is_le(file.at(a), file.at(b))

# the same path twice is the same file twice, and a package holds it once
def dedup.pick(same: Bool, h: File, r: List<&2, File>) -> List<&2, File>:
  match same:
    case True{}:
      r
    case False{}:
      h <> r

# a file against the deduplicated files that follow it
def dedup.head(+h: File, r: List<&2, File>) -> List<&2, File>:
  match r:
    case []:
      [h]
    case Con{+b, t}:
      dedup.pick(String.eq(file.at(h), file.at(b)), h, b <> t)

# a sorted file list with the repeats dropped
def dedup(fs: List<&2, File>) -> List<&2, File>:
  match fs:
    case []:
      []
    case Con{h, t}:
      dedup.head(h, dedup(t))

# where a file goes among the files already in order: before the one it is not
# after, otherwise behind it. The rest of the insertion is a parameter, because
# two defs that call each other are not allowed.
def file.ins.put(le: Bool, x: File, h: File, t: List<&2, File>,
  rest: List<&2, File>) -> List<&2, File>:
  match le:
    case True{}:
      x <> (h <> t)
    case False{}:
      h <> rest

# a file inserted into a list already in path order
def file.ins(fs: List<&2, File>, +x: File) -> List<&2, File>:
  match fs:
    case []:
      [x]
    case Con{+h, +t}:
      file.ins.put(file.le(x, h), x, h, t, file.ins(t, x))

# a file list in path order. Insertion rather than Base's `List.sort`: that one
# is a fuelled bottom-up merge sort, whose recursion Bend cannot check, so it
# is reported as unsafe and every proof downstream of it inherits the report.
# An insertion sort shrinks its list at every step, so Bend checks it, and a
# package's file set is small enough that the cost is not felt.
def file.sort(fs: List<&2, File>) -> List<&2, File>:
  match fs:
    case []:
      []
    case Con{+h, t}:
      file.ins(file.sort(t), h)

# the files of a package, in path order and each one once
def files_of(fs: List<&2, File>) -> List<&2, File>:
  dedup(file.sort(fs))

# a path that leaves the package behind, which no package may hold
def escapes(+at: String) -> Bool:
  Bool.or(String.starts_with(at, "/"), String.starts_with(at, ".."))

# one step of the search, with the head's answer in hand. A search that puts
# its recursion in an arm of a `Bool.pick` is not a search: the arm is built
# whatever the answer, so the first escaping path still costs a walk of every
# file after it. The thunk is what makes the stop a stop.
def escaped.step(here: Bool, at: String, rest: Unit -> String) -> String:
  match here:
    case True{}:
      at
    case False{}:
      rest(Unit{})

# the first file whose path leaves the package, or "" when none does
def escaped(fs: List<&2, File>) -> String:
  match fs:
    case []:
      ""
    case +h <> t:
      +at = file.at(h)
      escaped.step(escapes(at), at, _u => escaped(t))

# one `<sha256> <path>` line
def manifest.line(f: File) -> String:
  File{at, sum} = f
  sum ++ " " ++ at ++ "\n"

# every line of a manifest
def manifest.lines(fs: List<&2, File>) -> String:
  match fs:
    case []:
      ""
    case h <> t:
      manifest.line(h) ++ manifest.lines(t)

# the manifest text is the package's identity, and bend checks a fetched
# manifest against the first 32 hex characters of its sha256
def manifest_of(fs: List<&2, File>) -> String:
  manifest.lines(files_of(fs))

# the `0x` name a file set is published under
def hash_of(fs: List<&2, File>) -> String:
  "0x" ++ String.take(Sha.hex(manifest_of(fs)), 32n)

# the verdict, with the escaping path's name already found. `hash_of` is a
# sha256 over the whole package manifest; under a `Bool.pick` a package that
# escapes its root paid for that hash before being refused for it.
def pkg.judge.step(ok: Bool, bad: String, root: String,
  +fs: List<&2, File>) -> IO(Pkg):
  match ok:
    case True{}:
      IO.pure(Pkg, Pkg{hash_of(fs), root, files_of(fs)})
    case False{}:
      IO.die(Pkg, 1, "ez: " ++ bad ++ " escapes the package")

# a file set that stays inside its package becomes one; one that does not stops
# the command
def pkg.judge(+bad: String, root: String, +fs: List<&2, File>) -> IO(Pkg):
  pkg.judge.step(String.is_empty(bad), bad, root, fs)

# the found files, placed under the package root and judged
def pkg.place(root: String, pre: String, fs: List<&2, Found>) -> IO(Pkg):
  +files = files_of(placed(pre, fs))
  pkg.judge(escaped(files), root, files)

# the package an entry file would be published as: every module it reaches,
# every foreign body beside them, and the hash over their manifest
def pkg_of(+entry: String) -> IO(Pkg):
  do IO<Pkg>:
    st : State <- walk(U32.to_nat(100000), P.base(entry), [Task{entry, ""}],
      State{[], []})
    +fs : List<&2, Found> <- IO.pure(List<&2, Found>, state.out(st))
    +n : Nat <- IO.pure(Nat, climb(fs))
    pre : String <- anc(n, P.dir(entry))
    pkg.place(P.climb(n, P.dir(entry)), pre, fs)

# the hash that names a package
def pkg.hash(p: Pkg) -> String:
  Pkg{h, _root, _fs} = p
  h

# the directory a package's file paths are written from
def pkg.root(p: Pkg) -> String:
  Pkg{_h, root, _fs} = p
  root

# the files a package holds
def pkg.files(p: Pkg) -> List<&2, File>:
  Pkg{_h, _root, fs} = p
  fs

# the sha256 recorded for a file
def file.sum(f: File) -> String:
  File{_at, sum} = f
  sum
