# ez/gate: one binary a project, rather than one a test. bend has no
# incremental compile, so every build pays for the whole import closure, and a
# project's tests import nearly the same one. This is the aggregate that pays
# it once: `<project>/.gate/all.bend` imports every test of the project and
# calls each `main` behind a marker line. Each test still answers for its own
# `#|` trailer — the runner cuts the run's output on the markers and hands each
# slice to the test that asked for it — so only the compiling is shared.
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

# where a project's aggregate source is written. It sits beside the tests it
# imports so that `../tests/<name>.bend` reaches them whatever the project is
# called: a hyphen in an import path breaks the JS backend, and this way no
# directory name ever appears in one. The two lanes get a file each, since a
# test headed `# lanes: native` belongs in one of them and not the other.
def src(+dir: String, +name: String) -> String:
  dir ++ "/.gate/" ++ name ++ ".bend"

# where a project's aggregate binary lands
def bin(+dir: String) -> String:
  dir ++ "/.gate/all.bin"

# the directory an aggregate needs before it can be written
def at(+dir: String) -> String:
  dir ++ "/.gate"

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
  "# the runner cuts this run's output on the marker lines.\n" ++
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

# tests in one binary share a process, so a test that reads its own command
# line cannot be aggregated: `IO.args()` would hand it the aggregate's
# arguments. Reading the environment is fine — it is the same environment
# either way — and no test in this repo reads either.
def solitary(+text: String) -> Bool:
  String.contains(text, "IO.args")
