# pkg/pkg: the package a `bend <entry> --publish` would upload, computed
# without publishing: the file set, their sha256s, and the `0x<hash>` that names
# them. This mirrors `pkg_files` and the hash in bend's `cli_publish`.
# `tests/publish.sh` pins it against the real thing by running `bend --publish`
# at a local hub, so drift fails the gate rather than the ecosystem.
#
# The walk is pure: `of` computes the package from a checkout's files alone,
# which is what `ez add` in planner form will run, and `pkg_of` and `pkg_in`
# run the same walk given nothing, answering each file it asks for from disk.
# Bend refuses an import cycle, and this module both defines the file list the
# walk hashes and runs it, so the walk lives here rather than in a module of
# its own.
import Base
import ../io/file.bend as F
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
def words(line: String) -> List<&2, String>:
  words.keep(String.split(line, ' '))

# a character bend's loader reads as white space in an import line. The
# loader trims each line of a file's header and splits an import on `\s+`,
# JavaScript's white space: tab, line feed, vertical tab, form feed, carriage
# return and space, the no-break space, and the Unicode space separators, the
# line and paragraph separators and the byte order mark. A zero-width space
# or a next-line character is not one, and bend refuses an import it holds.
def blank(+ch: Char) -> Bool:
  match ch:
    case Chr{+x}:
      Bool.or(Bool.or(U32.is_eq(x, 32), Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13))),
        Bool.or(Bool.or(U32.is_eq(x, 160), U32.is_eq(x, 5760)),
          Bool.or(Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8202)),
            Bool.or(Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)),
              Bool.or(Bool.or(U32.is_eq(x, 8239), U32.is_eq(x, 8287)),
                Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279)))))))

# the front of a line, past one character that may be blank
def trim.front.at(skip: Bool, head: Char, tail: String, rest: Unit -> String) -> String:
  match skip:
    case True{}:
      rest(Unit{})
    case False{}:
      SCon{head, tail}

# a line with its leading blanks dropped
def trim.front(line: String) -> String:
  match line:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      trim.front.at(blank(h), h, t, _u => trim.front(t))

# a character kept before the rest of a line with its trailing blanks
# dropped. The character goes too when it is blank and nothing follows it.
def trim.back.at(gone: Bool, head: Char, rest: String) -> String:
  match gone:
    case True{}:
      SNil{}
    case False{}:
      SCon{head, rest}

# a line with its trailing blanks dropped, read from the front, so that the
# trim of a line is a walk over it rather than over its reverse
def trim.back(line: String) -> String:
  match line:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      +rest = trim.back(t)
      trim.back.at(Bool.and(blank(h), String.is_empty(rest)), h, rest)

# a line with the blanks at either end dropped, as bend's loader trims it
def trim(line: String) -> String:
  trim.back(trim.front(line))

# the fields of a line read so far: the field under way, and the fields after
# it
type Cut is Data:
  Cut{field: String, after: List<&2, String>}

# a field put before the fields after it, unless it is empty
def cut.put(field: String, after: List<&2, String>) -> List<&2, String>:
  match field:
    case SNil{}:
      after
    case SCon{h, t}:
      SCon{h, t} <> after

# one character before the fields read so far: a blank ends the field under
# way, and anything else extends it
def cut.at(gap: Bool, head: Char, sofar: Cut) -> Cut:
  match gap:
    case True{}:
      Cut{field, after} = sofar
      Cut{"", cut.put(field, after)}
    case False{}:
      Cut{field, after} = sofar
      Cut{SCon{head, field}, after}

# a line cut at its blanks, read from the back
def cut(line: String) -> Cut:
  match line:
    case SNil{}:
      Cut{"", []}
    case SCon{+h, t}:
      cut.at(blank(h), h, cut(t))

# a line's fields once it is cut: the one under way before the rest
def cut.all(sofar: Cut) -> List<&2, String>:
  Cut{field, after} = sofar
  cut.put(field, after)

# the fields of an import line: what is left between its runs of blanks, as
# bend's loader splits it. `words` splits on spaces alone, which is how a
# manifest line is split.
def fields(line: String) -> List<&2, String>:
  cut.all(cut(line))

# the nth word, or "" when the line is shorter than that. Both the list and the
# count are scrutinised together, so the walk needs no helper to branch through.
def word(ws: List<&2, String>, index: Nat) -> String:
  match ws index:
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

# `import Base` brings in the prelude, which is no part of any package. bend
# lets a comment follow it, and a comment names no module.
def base_of(+ws: List<&2, String>) -> Stmt:
  base_of.step(
    Bool.and(Bool.or(Nat.is_eq(List.length(&2, String, ws), 2n),
        String.starts_with(word(ws, 2n), "#")),
      Bool.and(String.eq(word(ws, 0n), "import"), String.eq(word(ws, 1n), "Base"))),
    ws)

# a line that neither opens nor ends the header
def quiet(+line: String) -> Bool:
  Bool.or(String.is_empty(line), String.starts_with(line, "#"))

# a line that says nothing about the header, decided. `fields` is a walk
# over the line that cuts it at its blanks, and this is the arm it hangs
# from: every blank line and every comment line of every `.bend` file of the
# project and of every package it resolves used to be split into words and
# classified, which is most of the lines ez ever reads.
def stmt_of.quiet(skip: Bool, +line: String) -> Stmt:
  match skip:
    case True{}:
      SNone{}
    case False{}:
      base_of(fields(line))

# the rest of a line, past one character that may be skipped
def foreign.gap.at(skip: Bool, head: Char, tail: String, rest: Unit -> String) -> String:
  match skip:
    case True{}:
      rest(Unit{})
    case False{}:
      SCon{head, tail}

# a line past its `import`, with the spaces, tabs and carriage returns bend's
# parser skips between the word and the path dropped
def foreign.gap(line: String) -> String:
  match line:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      foreign.gap.at(Bool.or(Char.is_eq(h, ' '), Bool.or(Char.is_eq(h, '\t'),
        Char.is_eq(h, '\r'))), h, t, _u => foreign.gap(t))

# the quoted path of a foreign import, once its `import` and the gap after
# it are gone
def foreign.path(+rest: String) -> String:
  String.take(String.drop(rest, 1n), Nat.sub(String.length(rest), 2n))

# whether what follows a line's `import` is a quoted path
def foreign.quoted(+rest: String) -> Bool:
  Bool.and(String.starts_with(rest, "\""), String.ends_with(rest, "\""))

# the foreign import decided. The rest of the cascade hangs off the False arm
# rather than sitting in an argument, so a line that is a foreign import pays
# for nothing below it.
def stmt_of.foreign(here: Bool, +line: String) -> Stmt:
  match here:
    case True{}:
      SForeign{foreign.path(foreign.gap(String.drop(line, 6n)))}
    case False{}:
      stmt_of.quiet(quiet(line), line)

# a trimmed line classified. A foreign import is tested first: it lives in a
# def's body, long after the header has ended. bend's parser reads the word
# `import`, skips spaces, tabs and carriage returns, and reads a quoted path.
def stmt_of(+line: String) -> Stmt:
  stmt_of.foreign(
    Bool.and(String.starts_with(line, "import"),
      foreign.quoted(foreign.gap(String.drop(line, 6n)))), line)

# a module named after the header has ended is not part of the header, so the
# line is ignored rather than followed
def scan.mod(+head: Bool, spec: String, mods: List<&2, String>, foreign: List<&2, String>) -> Head:
  match head:
    case True{}:
      Head{True{}, spec <> mods, foreign}
    case False{}:
      Head{False{}, mods, foreign}

# the state once a line has been classified
def scan.go(st: Head, stmt: Stmt) -> Head:
  Head{head, mods, foreign} = st
  match stmt:
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
  scan.go(st, stmt_of(trim(raw)))

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
def scan.mods(scanned: Scan) -> List<&2, String>:
  Scan{mods, _foreign} = scanned
  mods

# the foreign bodies a scan found
def scan.foreign(scanned: Scan) -> List<&2, String>:
  Scan{_mods, foreign} = scanned
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

# a module import as the file to visit next, or nothing when it names a hub
# package
def task_of(+dir: String, +nd: String, +spec: String) -> List<&2, Task>:
  Bool.pick(List<&2, Task>, is_hub(spec), [],
    [Task{P.join(dir, spec), P.unbend(P.join(nd, spec))}])

# every module a file imports, as the files to visit next
def tasks(+dir: String, +nd: String, ms: List<&2, String>) -> List<&2, Task>:
  match ms:
    case []:
      []
    case h <> t:
      List.append(&2, Task, task_of(dir, nd, h), tasks(dir, nd, t))

# the directory a module's own imports are named from. The entry is the package
# root, so its modules are named from nowhere in particular.
def nsdir(+ns: String) -> String:
  Bool.pick(String, String.is_empty(ns), "", P.dir(ns))

# the entry file is written under its own base name; every other module under
# the path it was reached through
def raw_of(+ns: String, eb: String) -> String:
  Bool.pick(String, String.is_empty(ns), eb, ns ++ ".bend")

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
def seen.has(xs: List<&2, String>, +want: String) -> Bool:
  match xs:
    case []:
      False{}
    case +h <> t:
      seen.has.step(String.eq(h, want), _u => seen.has(t, want))

# a found file, placed under whatever the package re-rooted at
def file_of(+pre: String, hit: Found) -> File:
  Found{raw, sum} = hit
  File{P.join(pre, raw), sum}

# every found file, placed
def placed(+pre: String, fs: List<&2, Found>) -> List<&2, File>:
  match fs:
    case []:
      []
    case h <> t:
      file_of(pre, h) <> placed(pre, t)

# where a file sits inside its package
def file.at(item: File) -> String:
  File{at, _sum} = item
  at

# a package's files are written in path order, so the manifest of a package is
# the same text whoever computes it
def file.le(left: File, right: File) -> Bool:
  String.is_le(file.at(left), file.at(right))

# the same path twice is the same file twice, and a package holds it once
def dedup.pick(same: Bool, head: File, rest: List<&2, File>) -> List<&2, File>:
  match same:
    case True{}:
      rest
    case False{}:
      head <> rest

# a file against the deduplicated files that follow it
def dedup.head(+head: File, rest: List<&2, File>) -> List<&2, File>:
  match rest:
    case []:
      [head]
    case Con{+b, t}:
      dedup.pick(String.eq(file.at(head), file.at(b)), head, b <> t)

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
def file.ins.put(le: Bool, item: File, head: File, tail: List<&2, File>, rest: List<&2, File>) -> List<&2, File>:
  match le:
    case True{}:
      item <> (head <> tail)
    case False{}:
      head <> rest

# a file inserted into a list already in path order
def file.ins(fs: List<&2, File>, +item: File) -> List<&2, File>:
  match fs:
    case []:
      [item]
    case Con{+h, +t}:
      file.ins.put(file.le(item, h), item, h, t, file.ins(t, item))

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
def manifest.line(item: File) -> String:
  File{at, sum} = item
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

# ---------------------------------------------------------------------------
# the walk

# one file of a checkout: its path from the checkout's top, and its text
type Source is Data:
  Source{at: String, text: String}

# the files a walk is given. A whole tree is every file of a checkout, so a
# path it does not hold is not there. A partial one is what has been read so
# far, with the paths that were asked for and found missing; any other path
# is one the walk was not given, and it asks for it.
type Tree is Data:
  Tree{whole: Bool, files: List<&2, Source>, gone: List<&2, String>}

# what a tree says of a path: here with its text, not there, or not given
type Look is Data:
  Here{text: String}
  Absent{}
  Unasked{}

# a file of the package as the walk found it: the name it takes inside the
# package, and its text
type Hit is Data:
  Hit{raw: String, text: String}

# why the walk stopped, or that it has not: a module imported and not there,
# an import that climbs out of the checkout, a file the walk was not given,
# or fuel run out with files still queued
type Stop is Data:
  Going{}
  Missing{at: String}
  Climbs{at: String}
  Asking{at: String}
  Spent{}

# the walk so far: the files already visited, what was found, whether it has
# stopped, and the files still to visit
type State is Data:
  State{seen: List<&2, String>, out: List<&2, Hit>, stop: Stop, queue: List<&2, Task>}

# what the walk made of a tree: the package, the file it needs next, or why
# there is no package. A package is its hash, the directory its paths are
# written from, the files it lays with their texts, and those files weighed,
# in path order, which is what its manifest lists.
type Walked is Data:
  Walked{hash: String, root: String, files: List<&2, Source>, sums: List<&2, File>}
  Asks{at: String}
  Refused{why: String}

# a path of the project, as it is written inside a package rooted at `root`:
# the path itself under the project's own root, and the path with the root's
# directories taken off otherwise. The hub serves a package's files at these
# paths, so `ez add` and `ez publish` both name the entry by it.
def inside(+root: String, +path: String) -> String:
  Bool.pick(String, String.eq(root, "."), path,
    String.drop(path, (String.length(root) + 1n : Nat)))

# one step of a lookup, with the head's answer in hand. The rest arrives as a
# thunk, so a hit ends the search.
def look.step(hit: Bool, text: String, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{text}
    case False{}:
      rest(Unit{})

# a file list's text for a path, first in the list, or None when it has none
def look(fs: List<&2, Source>, +at: String) -> Maybe<&2, String>:
  match fs:
    case []:
      None{}
    case Source{+h, text} <> t:
      look.step(String.eq(h, at), text, _u => look(t, at))

# a path that was asked for and found missing is not there; one that was not
# asked for is not given
def find.asked(asked: Bool) -> Look:
  match asked:
    case True{}:
      Absent{}
    case False{}:
      Unasked{}

# a path the files do not hold: not there in a whole tree, and in a partial
# one unless it was asked for already
def find.miss(whole: Bool, gone: List<&2, String>, +at: String) -> Look:
  match whole:
    case True{}:
      Absent{}
    case False{}:
      find.asked(seen.has(gone, at))

# a path the files hold is here
def find.got(got: Maybe<&2, String>, whole: Bool, gone: List<&2, String>, +at: String) -> Look:
  match got:
    case Some{text}:
      Here{text}
    case None{}:
      find.miss(whole, gone, at)

# what a tree says of a path
def find(tree: Tree, +at: String) -> Look:
  Tree{whole, files, gone} = tree
  find.got(look(files, at), whole, gone, at)

# a checkout-relative path that climbs above the checkout's top
def outside(+at: String) -> Bool:
  +n = P.norm(at)
  Bool.or(String.eq(n, ".."), String.starts_with(n, "../"))

# a foreign body the tree holds, or nothing when it is not there. bend uploads
# only the ones that are there. It is named the way the module importing it
# is named, from that module's own directory: `bend --publish` writes
# `src/util/beep.c` for a body imported by `src/util/math.bend`.
def foreign.put(got: Look, +raw: String) -> List<&2, Hit>:
  match got:
    case Here{text}:
      [Hit{raw, text}]
    case Absent{}:
      []
    case Unasked{}:
      []

# every foreign body a file imports, named from the importing module's
# directory
def foreigns(+tree: Tree, +dir: String, +nd: String, ats: List<&2, String>) -> List<&2, Hit>:
  match ats:
    case []:
      []
    case +h <> t:
      List.append(&2, Hit, foreign.put(find(tree, P.join(dir, h)), P.join(nd, h)),
        foreigns(tree, dir, nd, t))

# a foreign body inside the checkout stops the walk only when it was not given
def foreign.asked(got: Look, +at: String, rest: Unit -> Stop) -> Stop:
  match got:
    case Here{_text}:
      rest(Unit{})
    case Absent{}:
      rest(Unit{})
    case Unasked{}:
      Asking{at}

# a foreign body that climbs out of the checkout stops the walk, naming it
def foreign.judge(out: Bool, +tree: Tree, +at: String, +raw: String, rest: Unit -> Stop) -> Stop:
  match out:
    case True{}:
      Climbs{raw}
    case False{}:
      foreign.asked(find(tree, at), at, rest)

# the first foreign body of a file that stops the walk, or `Going` when none
# does
def foreign.check(+tree: Tree, +dir: String, +nd: String, ats: List<&2, String>) -> Stop:
  match ats:
    case []:
      Going{}
    case +h <> t:
      +at = P.join(dir, h)
      foreign.judge(outside(at), tree, at, P.join(nd, h),
        _u => foreign.check(tree, dir, nd, t))

# a file whose foreign bodies are all settled: itself and its foreign bodies
# found, and the modules it imports put at the front of the queue, so the walk
# goes depth first the way bend's does. A foreign body that stops the walk
# leaves the file queued, so an answered question visits it again.
def visit.put(
  fstop: Stop,
  +tree: Tree,
  +sc: Scan,
  +text: String,
  +file: String,
  +ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Hit>,
  rest: List<&2, Task>
) -> State:
  match fstop:
    case Going{}:
      +d = P.dir(file)
      +nd = nsdir(ns)
      State{file <> seen,
        Hit{raw_of(ns, eb), text} <> List.append(&2, Hit,
          foreigns(tree, d, nd, scan.foreign(sc)), out),
        Going{},
        List.append(&2, Task, tasks(d, nd, scan.mods(sc)), rest)}
    case Missing{at}:
      State{seen, out, Missing{at}, Task{file, ns} <> rest}
    case Climbs{at}:
      State{seen, out, Climbs{at}, Task{file, ns} <> rest}
    case Asking{at}:
      State{seen, out, Asking{at}, Task{file, ns} <> rest}
    case Spent{}:
      State{seen, out, Spent{}, Task{file, ns} <> rest}

# a file that is in the tree, scanned, with its foreign bodies checked first
def visit.found(
  +tree: Tree,
  +text: String,
  +file: String,
  +ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Hit>,
  rest: List<&2, Task>
) -> State:
  +sc = scan(text)
  visit.put(foreign.check(tree, P.dir(file), nsdir(ns), scan.foreign(sc)),
    tree, sc, text, file, ns, eb, seen, out, rest)

# a module that is imported and not there stops the walk, since a package
# missing a file is not the package bend would publish. One the walk was not
# given stops it too, as a question, with the module still queued.
def visit.have(
  got: Look,
  +tree: Tree,
  +file: String,
  +ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Hit>,
  rest: List<&2, Task>
) -> State:
  match got:
    case Absent{}:
      State{seen, out, Missing{file}, rest}
    case Unasked{}:
      State{seen, out, Asking{file}, Task{file, ns} <> rest}
    case Here{text}:
      visit.found(tree, text, file, ns, eb, seen, out, rest)

# the name an import that climbs out is refused under: the path it was
# reached through, or the entry's own path
def climbs.name(+ns: String, +file: String) -> String:
  Bool.pick(String, String.is_empty(ns), file, ns ++ ".bend")

# a module above the checkout's top is refused rather than read: the package
# would be named after directories of whatever machine walked it
def visit.in(
  out: Bool,
  +tree: Tree,
  +file: String,
  +ns: String,
  eb: String,
  seen: List<&2, String>,
  outs: List<&2, Hit>,
  rest: List<&2, Task>
) -> State:
  match out:
    case True{}:
      State{seen, outs, Climbs{climbs.name(ns, file)}, rest}
    case False{}:
      visit.have(find(tree, file), tree, file, ns, eb, seen, outs, rest)

# a file already visited keeps the name it was first reached through, the way
# bend's own walk does
def visit.go(
  hit: Bool,
  +tree: Tree,
  +file: String,
  ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Hit>,
  rest: List<&2, Task>
) -> State:
  match hit:
    case True{}:
      State{seen, out, Going{}, rest}
    case False{}:
      visit.in(outside(file), tree, file, ns, eb, seen, out, rest)

# the next file of the queue visited, or the walk as it is when the queue is
# empty
def step.pop(
  +tree: Tree,
  eb: String,
  +seen: List<&2, String>,
  out: List<&2, Hit>,
  stop: Stop,
  queue: List<&2, Task>
) -> State:
  match queue:
    case []:
      State{seen, out, stop, []}
    case Task{+file, ns} <> t:
      visit.go(seen.has(seen, file), tree, file, ns, eb, seen, out, t)

# the walk as one step that does not recurse
def step(+tree: Tree, eb: String, st: State) -> State:
  State{seen, out, stop, queue} = st
  step.pop(tree, eb, seen, out, stop, queue)

# whether the walk has not stopped
def stop.going(stop: Stop) -> Bool:
  match stop:
    case Going{}:
      True{}
    case Missing{_at}:
      False{}
    case Climbs{_at}:
      False{}
    case Asking{_at}:
      False{}
    case Spent{}:
      False{}

# whether the walk is over: its queue is empty, or it has stopped
def walk.done(+st: State) -> Bool:
  State{_seen, _out, stop, queue} = st
  Bool.or(List.is_empty(&2, Task, queue), Bool.not(stop.going(stop)))

# the walk as it is when it is over, or one step further when it is not. The
# rest of the walk arrives as a function, since a def may not call itself from
# another def.
def walk.more(done: Bool, st: State, go: State -> State) -> State:
  match done:
    case True{}:
      st
    case False{}:
      go(st)

# the fuel ran out: a walk that is over stays as it is, and one with files
# still queued is spent, so it is refused rather than hashed short
def walk.spent(done: Bool, st: State) -> State:
  match done:
    case True{}:
      st
    case False{}:
      State{seen, out, _stop, queue} = st
      State{seen, out, Spent{}, queue}

# every file of the package reached from the entry, the step iterated under
# fuel, until the walk is over or stops
def walk(fuel: Nat, +tree: Tree, +eb: String, +st: State) -> State:
  match fuel:
    case 0n:
      walk.spent(walk.done(st), st)
    case 1n+f:
      walk.more(walk.done(st), st, now => walk(f, tree, eb, step(tree, eb, now)))

# the walk before its first step: the entry queued, under no name of its own
def start(+entry: String) -> State:
  State{[], [], Going{}, [Task{entry, ""}]}

# ---------------------------------------------------------------------------
# the package a walk found

# a found file weighed: its name and the sha256 of its text
def hit.sum(item: Hit) -> Found:
  Hit{raw, +text} = item
  Found{raw, Sha.hex(text)}

# every found file weighed
def hit.sums(fs: List<&2, Hit>) -> List<&2, Found>:
  match fs:
    case []:
      []
    case h <> t:
      hit.sum(h) <> hit.sums(t)

# a found file placed under whatever the package re-rooted at, with its text
def laid.one(+pre: String, item: Hit) -> Source:
  Hit{raw, text} = item
  Source{P.join(pre, raw), text}

# every found file placed, with its text
def laid(+pre: String, fs: List<&2, Hit>) -> List<&2, Source>:
  match fs:
    case []:
      []
    case h <> t:
      laid.one(pre, h) <> laid(pre, t)

# a laid file weighed: its path and the sha256 of its text. This is what a
# plan's reader would compute from the files a `Lay` writes.
def laid.sum(src: Source) -> File:
  Source{at, +text} = src
  File{at, Sha.hex(text)}

# every laid file weighed
def laid.sums(fs: List<&2, Source>) -> List<&2, File>:
  match fs:
    case []:
      []
    case h <> t:
      laid.sum(h) <> laid.sums(t)

# how far a found file climbs out of the entry's directory
def hit.ups(item: Hit) -> Nat:
  Hit{raw, _text} = item
  P.ups(raw)

# the deepest climb any file of the package makes
def climb(fs: List<&2, Hit>) -> Nat:
  match fs:
    case []:
      0n
    case h <> t:
      Nat.max(hit.ups(h), climb(t))

# the found files named, once no path escapes the package
def made.judge(
  ok: Bool,
  +bad: String,
  +root: String,
  +pre: String,
  +fs: List<&2, File>,
  out: List<&2, Hit>
) -> Walked:
  match ok:
    case True{}:
      Walked{hash_of(fs), root, laid(pre, out), fs}
    case False{}:
      Refused{"ez: " ++ bad ++ " escapes the package"}

# the found files, placed under the components the package re-roots under
# and weighed once
def made.placed(+root: String, +pre: String, +out: List<&2, Hit>) -> Walked:
  +fs = files_of(placed(pre, hit.sums(out)))
  +bad = escaped(fs)
  made.judge(String.is_empty(bad), bad, root, pre, fs, out)

# a package that climbs re-roots under as many of the entry directory's
# trailing components as its deepest climb. The walk refuses an import that
# climbs out of the checkout, so there are always that many; a package that
# still climbs further is refused rather than named after nothing.
def made.anc(far: Bool, +levels: Nat, +dir: String, +out: List<&2, Hit>) -> Walked:
  match far:
    case True{}:
      Refused{"ez: the package climbs out of the checkout"}
    case False{}:
      made.placed(P.climb(levels, dir), P.tail(dir, levels), out)

# how many components a checkout-relative directory has: none for the
# checkout's top
def comps(+dir: String) -> Nat:
  +d = P.norm(dir)
  Bool.pick(Nat, Bool.or(String.eq(d, "."), String.is_empty(d)), 0n,
    List.length(&2, String, String.split(d, '/')))

# the deepest climb decided: none leaves the package at the entry's directory
def made.climb(+levels: Nat, +dir: String, +out: List<&2, Hit>) -> Walked:
  match levels:
    case 0n:
      made.placed(P.norm(dir), "", out)
    case 1n+p:
      made.anc(Nat.is_gt(1n+p, comps(dir)), 1n+p, dir, out)

# the walk's end judged: a walk that is over is the package, one that asks is
# a question, and every other stop is a refusal naming what stopped it
def made.go(stop: Stop, +entry: String, +out: List<&2, Hit>) -> Walked:
  match stop:
    case Going{}:
      made.climb(climb(out), P.dir(entry), out)
    case Missing{at}:
      Refused{"ez: " ++ at ++ " is imported but not there"}
    case Climbs{at}:
      Refused{"ez: the import " ++ at ++ " climbs out of the checkout"}
    case Asking{at}:
      Asks{at}
    case Spent{}:
      Refused{"ez: the walk from " ++ entry ++ " ran out of fuel"}

# the walk's end, judged
def made(+entry: String, st: State) -> Walked:
  State{_seen, out, stop, _queue} = st
  made.go(stop, entry, out)

# the package an entry of a tree would be published as, from the tree's
# files alone, with this much fuel
def of.tree(fuel: Nat, +entry: String, +tree: Tree) -> Walked:
  made(entry, walk(fuel, tree, P.base(entry), start(entry)))

# the same over a whole checkout
def of.fuel(fuel: Nat, +entry: String, +fs: List<&2, Source>) -> Walked:
  of.tree(fuel, entry, Tree{True{}, fs, []})

# the same, with the fuel `pkg_of` walks with
def of(+entry: String, +fs: List<&2, Source>) -> Walked:
  of.fuel(U32.to_nat(100000), entry, fs)

# ---------------------------------------------------------------------------
# the walk answered from disk

# a path read and found missing, added to what the walk was given
def tree.gone(tree: Tree, at: String) -> Tree:
  Tree{whole, files, gone} = tree
  Tree{whole, files, at <> gone}

# a file read, added to what the walk was given
def tree.have(tree: Tree, src: Source) -> Tree:
  Tree{whole, files, gone} = tree
  Tree{whole, src <> files, gone}

# what a read answered, added to what the walk was given
def tree.add(got: Maybe<&2, String>, tree: Tree, +at: String) -> Tree:
  match got:
    case None{}:
      tree.gone(tree, at)
    case Some{text}:
      tree.have(tree, Source{at, text})

# a walk that stopped to ask, taken up again where it stopped
def resume(st: State) -> State:
  State{seen, out, _stop, queue} = st
  State{seen, out, Going{}, queue}

# why a walk stopped
def state.stop(st: State) -> Stop:
  State{_seen, _out, stop, _queue} = st
  stop

# a walk's verdict as a package, with its root taken back under the checkout
# it was read from
def pkg.made(+top: String, got: Walked) -> IO(Pkg):
  match got:
    case Walked{hash, root, _files, sums}:
      IO.pure(Pkg, Pkg{hash, P.join(top, root), files_of(sums)})
    case Asks{at}:
      IO.die(Pkg, 1, "ez: the walk asked for " ++ at ++ " after it was answered")
    case Refused{why}:
      IO.die(Pkg, 1, why)

# a question read from disk and the walk carried on, or the walk's end judged
def pkg.next(
  stop: Stop,
  +top: String,
  +entry: String,
  +tree: Tree,
  +st: State,
  go: Tree -> State -> IO(Pkg)
) -> IO(Pkg):
  match stop:
    case Asking{+at}:
      do IO<Pkg>:
        m : Maybe<&2, String> <- F.read(P.join(top, at))
        go(tree.add(m, tree, at), resume(st))
    case Going{}:
      pkg.made(top, made(entry, st))
    case Missing{_at}:
      pkg.made(top, made(entry, st))
    case Climbs{_at}:
      pkg.made(top, made(entry, st))
    case Spent{}:
      pkg.made(top, made(entry, st))

# the walk over what has been read so far, and each file it asks for read
# and handed back, until it no longer asks
def pkg.ask(fuel: Nat, +top: String, +entry: String, +eb: String, +tree: Tree, st: State) -> IO(Pkg):
  match fuel:
    case 0n:
      IO.die(Pkg, 1, "ez: the walk from " ++ entry ++ " asked too many questions")
    case 1n+f:
      +now = walk(U32.to_nat(100000), tree, eb, st)
      pkg.next(state.stop(now), top, entry, tree, now,
        t => s => pkg.ask(f, top, entry, eb, t, s))

# the package an entry would be published as, walked over its checkout: the
# entry and every file the walk reaches are paths from `top`, read from disk
# as the walk asks for them. An import that climbs above `top` is refused.
def pkg.walk(+top: String, +entry: String) -> IO(Pkg):
  pkg.ask(U32.to_nat(100000), top, entry, P.base(entry), Tree{False{}, [], []},
    start(entry))

# the package an entry of a checkout would be published as
def pkg_in(+top: String, +entry: String) -> IO(Pkg):
  pkg.walk(top, P.norm(entry))

# an entry named from the working directory is walked over the working
# directory, and one named from the root over the whole file system
def pkg.from(abs: Bool, +entry: String) -> IO(Pkg):
  match abs:
    case True{}:
      pkg.walk("/", String.drop(entry, 1n))
    case False{}:
      pkg.walk("", entry)

# the package an entry file would be published as: every module it reaches,
# every foreign body beside them, and the hash over their manifest. A relative
# entry's checkout is the working directory, which is the project a command
# runs in.
def pkg_of(+entry: String) -> IO(Pkg):
  pkg.from(String.starts_with(entry, "/"), entry)

# the hash that names a package
def pkg.hash(package: Pkg) -> String:
  Pkg{h, _root, _fs} = package
  h

# the directory a package's file paths are written from
def pkg.root(package: Pkg) -> String:
  Pkg{_h, root, _fs} = package
  root

# the files a package holds
def pkg.files(package: Pkg) -> List<&2, File>:
  Pkg{_h, _root, fs} = package
  fs

# the sha256 recorded for a file
def file.sum(item: File) -> String:
  File{_at, sum} = item
  sum
