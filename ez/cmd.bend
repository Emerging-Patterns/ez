# ez/cmd: what each subcommand does. Everything that touches the network or the
# file system goes through run/run.bend, one process effect, because bend links
# no TLS and Base has neither mkdir nor readdir.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../lock/lock.bend as Lock
import ../lock/restore.bend as Restore
import ../git/git.bend as Git
import ./args.bend as Args
import ./env.bend as Env
import ./cap.bend as Cap

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the ledger on disk, parsed
def load() -> IO(M.Read):
  do IO<M.Read>:
    t : Maybe<&2, String> <- F.read(toml())
    return M.parse(F.text_of(t))

# a failed run must fail the command, or a script around it learns nothing
def report.exit(ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "")

# a run's output, printed, and its status turned into this program's
def report(+out: String) -> IO(Unit):
  do IO<Unit>:
    IO.write(R.text(out))
    report.exit(R.ok(out))

# the same, with a word in front of it for a run the kernel ended rather than
# the program. bend prints that all terms check before it emits any C, so a
# build killed at the cap is otherwise indistinguishable from one that worked
# and wrote nothing.
def report.capped(+why: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    IO.write(why ++ R.text(out))
    report.exit(R.ok(out))

# the entry file a ledger names, or "main.bend" when it names none
def entry.or(+e: String) -> String:
  Bool.pick(String, String.is_empty(e), "main.bend", e)

# the name a ledger gives the package, or `app` when there is no ledger to ask
def named(r: M.Read) -> String:
  match r:
    case M.Bad{_why}:
      "app"
    case M.Good{m}:
      M.Manifest{n, _e, _ds} = m
      n

# the entry file of a ledger that was read
def entry(r: M.Read) -> String:
  match r:
    case M.Bad{_why}:
      "main.bend"
    case M.Good{m}:
      M.Manifest{_n, e, _ds} = m
      entry.or(e)

# a ledger that would not parse stops the command before it does damage
def refuse(r: M.Read) -> IO(Unit):
  IO.die(Unit, 1, "ez: " ++ M.show(r))

# `ez check` and `ez run` are not capped, and `ez build` is. The wall
# `ez/cap.bend` exists for is bend's C backend: emitting the C for a large
# program peaked at 18.8 GB here and an uncapped one reached 35 GB. `ez check`
# emits JS and `ez run` interprets, so neither reaches that backend; and what
# `ez run` spends after that is the user's own program spending it, which is
# not ez's to ration.
#
# `bend f -o out` checks without running main. A clean file prints nothing at
# all, and a library entry, having no main, checks clean and then exits 1 with
# "no main to run" from the emit. A check failure throws before the emit, so
# that message can only follow a check that passed.
def check.passed(+out: String) -> Bool:
  Bool.or(R.ok(out), String.contains(R.text(out), "no main to run"))

# a passing check says so, since bend says nothing when it is happy
def check.said(passed: Bool, entry: String, text: String) -> IO(Unit):
  match passed:
    case True{}:
      IO.print("ok " ++ entry)
    case False{}:
      do IO<Unit>:
        IO.write(text)
        IO.die(Unit, 1, "")

# the entry checked, and never run
def check() -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +at : String <- IO.pure(String, entry(r))
    +out : String <- Env.exec(["bend", at, "-o", ".ez/check.js"])
    check.said(check.passed(out), at, R.text(out))

# where a build lands when nothing said: `bin/<package name>.out`. The name
# and not the entry file, because the entry is where a program starts and the
# name is what it is called — a package named `bolt` with its entry at
# `bolt/main.bend` builds `bin/bolt.out` and not `bin/main.out`.
def build.named(+name: String) -> String:
  "bin/" ++ name ++ ".out"

# where a build lands: what was asked for, or the default
def build.out(+at: String, +name: String) -> String:
  Bool.pick(String, String.is_empty(at), build.named(name), at)

# a native binary, named after the package. This is the one command that
# reaches bend's C backend, so it is the one that runs under the memory cap.
def build(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +r : M.Read <- load()
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +g : String <- Cap.gb()
    +out : String <- Cap.run(cap, ["bend", entry(r), "-o",
      build.out(Args.at(as, 0n), named(r))])
    report.capped(Cap.why(out, g), out)

# the entry run, which checks it first
def run(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +out : String <- Env.exec(List.append(&2, String, ["bend", entry(r)], as))
    report(out)

# every .bend file under the current directory, for the lock's roots
def sources() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["find", ".", "-name", "*.bend",
      "-not", "-path", "./.ez/*"])
    return Args.nonempty(String.lines(R.text(out)))

# the lock's path, which is fixed
def lockfile() -> String:
  "ez.lock.toml"

# the lock, rewritten from every root in the tree
def lock() -> IO(Unit):
  do IO<Unit>:
    srcs : List<&2, String> <- sources()
    text : String <- Lock.lock(srcs)
    wrote : Bool <- F.write(lockfile(), text)
    report.exit(wrote)

# BEND_LIB filled from the lock, with nothing re-resolved
def fetch() -> IO(Unit):
  Restore.restore(lockfile())

# the name a new ledger takes: what was asked for, or `app`
def init.name(+at: String) -> String:
  Bool.pick(String, String.is_empty(at), "app", at)

# where the ignore rules go
def ignore() -> String:
  ".gitignore"

# everything ez writes into a project that is not the project's: the vendored
# packages, the test gate's shadow and its cache all live under one `.ez/`, and
# `ez build` drops a binary in `bin/<name>.out` unless it is told otherwise. A
# project whose first `ez check` leaves untracked output is a project whose
# owner has to work out for themselves which of it was theirs.
def init.rules(+name: String) -> List<&2, String>:
  [".ez/", build.named(name)]

# whether a file already states this rule, on a line of its own. A rule buried
# in a longer line is not the rule, so the comparison is against whole lines.
def stated(ls: List<&2, String>, +rule: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(String.eq(String.trim(h), rule), stated(t, rule))

# the rules a file does not already state, in order
def init.missing(rs: List<&2, String>, +ls: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = init.missing(t, ls)
      Bool.pick(List<&2, String>, stated(ls, h), more, h <> more)

# a file's text with a newline on the end, so what is appended to it starts on
# a line of its own. An empty file gets none, or the append would open with a
# blank line.
def init.tail(+text: String) -> String:
  Bool.pick(String, Bool.or(String.is_empty(text), String.ends_with(text, "\n")),
    text, text ++ "\n")

# the ignore file with the rules it lacks added under a line saying whose they
# are. What is already there is kept: the file is the project's, not ez's.
def init.ignored(+text: String, ms: List<&2, String>) -> String:
  init.tail(text) ++ "# written by ez\n" ++ String.join(ms, "\n") ++ "\n"

# nothing to add means nothing written, so a second `ez init` leaves the file
# it read exactly as it found it
def init.ignore.put(ms: List<&2, String>, +text: String) -> IO(Bool):
  match ms:
    case Nil{}:
      IO.pure(Bool, True{})
    case Con{h, t}:
      F.write(ignore(), init.ignored(text, h <> t))

# the project's ignore file, made or added to
def init.ignore(+name: String) -> IO(Bool):
  do IO<Bool>:
    g : Maybe<&2, String> <- F.read(ignore())
    +text : String <- IO.pure(String, F.text_of(g))
    init.ignore.put(init.missing(init.rules(name), String.lines(text)), text)

# a new project: a ledger naming this directory and its entry file, and the
# ignore rules for what ez will generate beside them
def init(+as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +name : String <- IO.pure(String, init.name(Args.at(as, 0n)))
    wrote : Bool <- F.write(toml(),
      Rend.show(M.Manifest{name, entry.or(Args.at(as, 1n)), []}))
    +kept : Bool <- init.ignore(name)
    report.exit(Bool.and(wrote, kept))

# the last path component
def add.base(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case Con{h, Nil{}}:
      h
    case Con{_h, t}:
      add.base(t)

# a dependency is named after its entry file, the way bend names an import
def add.alias(+at: String) -> String:
  String.take(add.base(String.split(at, '/')), Nat.sub(String.length(
    add.base(String.split(at, '/'))), 5n))

# a vendoring's answer as a ledger entry. The entry file is read twice, once
# for the name and once for itself, so it arrives through a parameter.
def add.dep.go(hash: String, url: String, rev: String, +at: String,
  tag: String) -> M.Dep:
  M.Dep{add.alias(at), hash, at, M.Git{url, rev, tag}}

# what a vendoring answered, as the ledger records it
def add.dep(g: Git.Got) -> M.Dep:
  Git.Got{h, u, v, e, t} = g
  add.dep.go(h, u, v, e, t)

# the ledger with this dependency written into it
def add.write(r: M.Read, d: M.Dep) -> IO(Unit):
  match r:
    case M.Bad{why}:
      refuse(M.Bad{why})
    case M.Good{m}:
      do IO<Unit>:
        wrote : Bool <- F.write(toml(), Rend.show(Rend.add(m, d)))
        report.exit(wrote)

# a git dependency vendored, and then recorded in the ledger under its own
# name. The vendoring comes first: a ledger naming a package that is not on
# disk is worse than no entry at all.
def add.go(+url: String, +ref: String, +entry: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Env.lib()
    g : Git.Got <- Git.vendor(lib, url, ref, entry)
    r : M.Read <- load()
    add.write(r, add.dep(g))

# `ez add <url> <rev|tag|branch> <entry.bend>`. All three are wanted: the
# entry is what the package's hash is computed from, and guessing it would
# name a different package.
def add(+as: List<&2, String>) -> IO(Unit):
  +at = Args.at(as, 2n)
  Bool.pick(IO(Unit), String.is_empty(at),
    IO.die(Unit, 1, "usage: ez add <url> <rev|tag|branch> <entry.bend>"),
    add.go(Args.at(as, 0n), Args.at(as, 1n), at))

# the ledger with a dependency dropped
def remove.write(r: M.Read, name: String) -> IO(Unit):
  match r:
    case M.Bad{why}:
      refuse(M.Bad{why})
    case M.Good{m}:
      do IO<Unit>:
        wrote : Bool <- F.write(toml(), Rend.show(Rend.remove(m, name)))
        report.exit(wrote)

# `ez remove <name>`
def remove(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    remove.write(r, Args.at(as, 0n))
