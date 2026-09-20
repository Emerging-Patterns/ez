# ez/gate: one binary a project, rather than one a test. bend has no
# incremental compile, so every build pays for the whole import closure, and a
# project's tests import nearly the same one. This is the aggregate that pays
# it once: `.ez/gate/<project>/ez.gate/all.bend` imports every test of the
# project and calls each `main` behind a marker line. Each test answers for its
# `#|` trailer — the runner cuts the run's output on the markers and hands each
# slice to the test that asked for it — so only the compiling is shared.
#
# Everything ez writes into a repo lives under one `.ez/`, and that is what
# makes `.ez/gate` a shadow of the repo rather than a plain directory of
# generated files. Two facts about bend force the shape:
#
# bend mangles the import path *text* into a JS identifier, so a hyphen
# anywhere in one emits a `.js` that compiles with status 0 and then throws
# `SyntaxError: Unexpected token '-'` when it is run. An aggregate under
# `.ez/gate` that reached back for its tests by name would write
# `../../../my-dir/tests/t.bend` and break on any project directory with a
# hyphen in it. So the aggregate keeps the text it has always had,
# `../tests/<name>.bend`, and never names its project at all. That is what the
# `ez.gate` directory under each project's shadow is for: somewhere to say
# `..` from.
#
# And bend normalizes `..` in an import lexically, before it opens anything, so
# a lone `tests` symlink beside the aggregate is not enough: a test's own
# `../x.bend` would be resolved against the link's path and land in the gate
# directory, where there is no x. The shadow answers that. Every entry of the
# repo root is linked into `.ez/gate`, every project that has tests is carved
# out of it as a real directory holding the aggregates and a link to each of
# the project's own entries, and so a test reached through the shadow sits at
# exactly the depth, and under exactly the names, its own imports were written
# against. The shadow's directories carry the repo's own names, hyphens and
# all, which is safe precisely because a shadow directory's name is the one
# thing that is never written into an import.
#
# The trailer walk lives here too, and this file imports nothing but Base, so a
# test of the runner's own text machinery costs a compile of that and no more.
import Base

# the line an aggregate prints before it calls a test's main. The output is cut
# on it, so it is a line no test would print itself.
def mark() -> String:
  "@@ez@@ "

# a trailer line kept, with its `#|` dropped, or a source line ignored
def want.put(is_want: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match is_want:
    case True{}:
      String.drop(h, 2n) <> rest
    case False{}:
      rest

# the `#|` lines of a source file, in order
def want(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      want.put(String.starts_with(h, "#|"), h, want(t))

# what a test file says its run must print
def trailer(text: String) -> String:
  String.join(want(String.lines(text)), "\n")

# the last of a list of strings, or "" when there is none
def last(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      h
    case Con{_h, t}:
      last(t)

# a path as `find` prints it, without the leading `./`
def rel(+path: String) -> String:
  Bool.pick(String, String.starts_with(path, "./"), String.drop(path, 2n), path)

# a path's last component
def base(+path: String) -> String:
  last(String.split(rel(path), '/'))

# every component of a path but the last two
def proj.go(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{_h, Nil{}}:
      Nil{}
    case Con{_h, Con{_g, Nil{}}}:
      Nil{}
    case Con{h, Con{g, Con{k, r}}}:
      h <> proj.go(Con{g, Con{k, r}})

# the project a test is of: its path without `tests/<name>.bend`. A top-level
# `tests/` test answers "", which is how the runner tells a unit test from an
# end-to-end one that drives git, nix and bend itself.
def proj(+path: String) -> String:
  String.join(proj.go(String.split(rel(path), '/')), "/")

# the one directory ez writes generated Bend into, and the repo's shape in
# miniature. It is rebuilt from nothing on every run, so a file deleted since
# the last one leaves no link behind.
def root() -> String:
  ".ez/gate"

# where a directory of the repo stands in the shadow. The root of the repo is
# the root of the shadow, which is what makes a test's `../..` land right.
def at(+dir: String) -> String:
  Bool.pick(String, String.is_empty(dir), root(), root() ++ "/" ++ dir)

# the directory inside a project's shadow that the aggregates are written to.
# It sits one level below the project rather than in it, so that an aggregate
# reaches its tests as `../tests/<name>.bend`.
#
# The `..` is not decoration. bend mangles a module's resolved path into the
# ids it emits, foreign ones included, and `file.bend` and `../file.bend` are
# the same file under two names: the short one collides with Base's own
# `File.write` and the C emit dies with `two names mangle to FID_FILE_WRITE`.
# The repo has always compiled under the long name, and this keeps it there.
#
# This name is never written into an import, which is why it may be anything
# and why a project directory with a hyphen in it still compiles. Nothing of
# the project is linked under it, so a project holding a directory of the same
# name loses nothing but the ability to import it from a test.
def agg.dir() -> String:
  "ez.gate"

# where a project's aggregates are written
def agg.at(+dir: String) -> String:
  at(dir) ++ "/" ++ agg.dir()

# where a project's aggregate source is written. The two lanes get a file each,
# since a test headed `# lanes: native` belongs in one of them and not the
# other.
def src(+dir: String, +name: String) -> String:
  agg.at(dir) ++ "/" ++ name ++ ".bend"

# where a project's aggregate binary lands
def bin(+dir: String) -> String:
  agg.at(dir) ++ "/all.bin"

# the real directory a shadow level is a copy of. `find` wants a name, and the
# repo root's name is `.`.
def of(+dir: String) -> String:
  Bool.pick(String, String.is_empty(dir), ".", dir)

# a path's prefixes, shortest first: `a/b` gives `a` and then `a/b`
def prefix.go(cs: List<&2, String>, +pre: String) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +next = Bool.pick(String, String.is_empty(pre), h, pre ++ "/" ++ h)
      next <> prefix.go(t, next)

# every directory on the way down to this one, itself last
def prefix(+dir: String) -> List<&2, String>:
  prefix.go(String.split(dir, '/'), "")

# every prefix of every project, with repeats still in
def spine(ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      List.append(&2, String, prefix(h), spine(t))

# whether a list already holds this string
def holds(ss: List<&2, String>, +s: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(String.eq(h, s), holds(t, s))

# the strings with each named once, the last of any repeat kept. Which one is
# kept does not matter: a level is a `mkdir -p` and a set of links, the links
# never name a carved directory, and so no level can undo another.
def once(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      +more = once(t)
      Bool.pick(List<&2, String>, holds(t, h), more, h <> more)

# every directory the shadow has to build for itself, the repo root first and
# then each project and each directory above it, named once
def levels(ds: List<&2, String>) -> List<&2, String>:
  "" <> once(spine(ds))

# whether a project's aggregates land in this directory or under it, which is
# what says the shadow must carve it out as a real directory rather than reach
# the whole of it with one link
def carved.one(+dir: String, +proj: String) -> Bool:
  Bool.or(String.eq(dir, proj), String.starts_with(proj, dir ++ "/"))

# the same asked of every project at once
def carved(+dir: String, ds: List<&2, String>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(carved.one(dir, h), carved(dir, t))

# whether the shadow has to keep this name for itself: a directory a project's
# aggregates land in, or the name the aggregates are written under
def kept(+at: String, +ds: List<&2, String>) -> Bool:
  Bool.or(carved(at, ds), String.eq(base(at), agg.dir()))

# the entries of a shadow level that a link can stand in for: everything the
# gate does not need the name of
def linked(es: List<&2, String>, +ds: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = linked(t, ds)
      Bool.pick(List<&2, String>, kept(rel(h), ds), more, h <> more)

# one test's import line, aliased by its position so two tests of the same name
# could not shadow each other
def agg.imports(ts: List<&2, String>, +i: Nat) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{+h, t}:
      "import ../tests/" ++ base(h) ++ " as T" ++ Nat.show(i) ++ "\n" ++
        agg.imports(t, (1n + i : Nat))

# one test's marker and the call behind it, in the order the imports were made
def agg.calls(ts: List<&2, String>, +i: Nat) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{+h, t}:
      "    IO.print(\"" ++ mark() ++ h ++ "\")\n" ++
        "    T" ++ Nat.show(i) ++ ".main()\n" ++ agg.calls(t, (1n + i : Nat))

# what the aggregate says about itself, to whoever finds it in a work directory
def agg.head(+dir: String) -> String:
  "# Written by `ez test`, and read by nothing else: every unit test of " ++
    dir ++ " in\n" ++
  "# one binary, so bend's whole-program compile is paid once for the project\n" ++
  "# rather than once a test. Each test still answers for its own `#|` trailer;\n" ++
  "# the runner cuts this run's output on the marker lines. This sits under a\n" ++
  "# shadow of " ++ dir ++ " made of symlinks, so `../tests` below is the\n" ++
  "# project's own, at the depth its own imports were written against.\n" ++
  "import Base\n"

# a project's tests as one program
def agg(+dir: String, +ts: List<&2, String>) -> String:
  agg.head(dir) ++ agg.imports(ts, 1n) ++
    "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" ++ agg.calls(ts, 1n)

# whether a line is one of the aggregate's markers
def marked(+line: String) -> Bool:
  String.starts_with(line, mark())

# a line kept or dropped
def put(drop: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match drop:
    case True{}:
      rest
    case False{}:
      h <> rest

# the state a marker line leaves behind: on when the marker is this test's, off
# when it is another's. Any other line leaves the state as it was.
def after(is_mark: Bool, hit: Bool, on: Bool) -> Bool:
  Bool.pick(Bool, is_mark, hit, on)

# the lines between this test's marker and the next marker. The state is
# decided once per line and used both for this line and for the next, the way
# quiet's walk does, so no second pass is needed. The list comes first because
# a self-call must shrink an argument before it changes one.
def slice.go(ls: List<&2, String>, +m: String, +on: Bool) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +next = after(marked(h), String.eq(h, m), on)
      put(Bool.or(marked(h), Bool.not(on)), h, slice.go(t, m, next))

# one test's own output, out of a run that holds every test's
def slice(text: String, +path: String) -> String:
  String.join(slice.go(String.lines(text), mark() ++ path, False{}), "\n")

# whether any marker was printed
def started.go(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(marked(h), started.go(t))

# whether the one binary ran at all. A test that runs as a `main` can still
# fail to import — a do-block binder sharing its name with a def in the same
# file is enough — and then the compile fails and no test of the project has
# been answered for. That is a failure of the whole project, named as one,
# never tests quietly skipped.
def started(text: String) -> Bool:
  started.go(String.lines(text))

# whether a line is a comment and nothing else
def commented(+line: String) -> Bool:
  String.starts_with(String.trim(line), "#")

# whether any line that is not a comment holds this
def coded(ls: List<&2, String>, +what: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Bool.and(Bool.not(commented(h)), String.contains(h, what)),
        coded(t, what))

# whether any of these lines begins with this
def headed.go(ls: List<&2, String>, +head: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(String.starts_with(h, head), headed.go(t, head))

# whether a file carries this header. A header is a line, and the difference
# is the whole point: a file holding the same words in a string literal, or in
# prose about headers, is saying nothing, and reading it as a header would
# change how the file is treated on the strength of a coincidence.
def headed(text: String, +head: String) -> Bool:
  headed.go(String.lines(text), head)

# tests in one binary share a process, so a test that reads its own command
# line cannot be aggregated: `IO.args()` would hand it the aggregate's
# arguments. Reading the environment is fine — it is the same environment
# either way — and no test in this repo reads either.
#
# What this can see is `IO.args` on a line that is not a comment. A test whose
# header explains why it does not read its command line is talking about it,
# not calling it, and reading that as a call fails a test that was never
# wrong. What this cannot see is the difference between code and a string
# literal: a test carrying `IO.args` inside one is still read as calling it.
# A scan over text cannot do better, and that is the safe side to be wrong on
# — a test wrongly held solitary is answered with a reason it can read, where
# a test wrongly aggregated would be answered with another test's output.
def solitary(+text: String) -> Bool:
  coded(String.lines(text), "IO.args")
