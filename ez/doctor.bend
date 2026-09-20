# ez/doctor: what would stop this project from building, said out loud. Each
# line reports what was found rather than a tick, because the useful answers
# here are values: which bend, which compiler, which packages are on disk, and
# which hashes the source and the ledger disagree about. A line that is a
# problem fails the command.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../manifest/manifest.bend as M
import ./args.bend as Args
import ./drift.bend as D
import ./sorted.bend as Sort
import ./env.bend as Env

# one thing doctor looked at: what to print, and whether it is a problem
type Note is Data:
  Note{wrong: Bool, line: String}

# the lock's path. It is named once so the file's format and name are one edit.
def lock() -> String:
  "ez.lock.toml"

# the ledger's path
def toml() -> String:
  "ez.toml"

# a count with its noun, kept in agreement
def plural(+n: Nat, one: String, many: String) -> String:
  Nat.show(n) ++ " " ++ Bool.pick(String, Nat.is_eq(n, 1n), one, many)

# the first line of what a program printed
def banner.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> t:
      h

# a version banner, which is one line however many a program prints
def banner(text: String) -> String:
  banner.of(String.lines(text))

# what a version run said about the program it ran
def probe.note(ok: Bool, name: String, +text: String) -> Note:
  match ok:
    case True{}:
      Note{False{}, name ++ ": " ++ banner(text)}
    case False{}:
      Note{True{}, name ++ ": not on PATH"}

# a program asked for its version, which answers both whether it is there and
# which one it is. bend's check report changed wording between 2.0.16 and
# 2.0.18, and the native lane needs a C compiler, so the version is the finding.
def probe(+name: String) -> IO(Note):
  do IO<Note>:
    +out : String <- R.exec([name, "--version"])
    return probe.note(R.ok(out), name, R.text(out))

# the C compiler the native lane will use: `$CC` when it is set, else `cc`.
# Same source and a different compiler is a different binary, so doctor names it
def cc.name(+v: String) -> String:
  Bool.pick(String, String.is_empty(v), "cc", v)

# the C compiler, by the name the toolchain will reach for
def cc() -> IO(Note):
  do IO<Note>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("CC")
    probe(cc.name(Args.text_of(r)))

# what the ledger turned out to be
def toml.note(r: M.Read) -> Note:
  match r:
    case M.Bad{why}:
      Note{True{}, "ez.toml: " ++ why}
    case M.Good{m}:
      M.Manifest{n, e, ds} = m
      Note{False{}, "ez.toml: " ++ n ++ ", entry " ++ e ++ ", " ++
        plural(List.length(&2, M.Dep, ds), "dependency", "dependencies")}

# the ledger on disk, parsed. Read here rather than borrowed from ez/cmd.bend,
# so doctor depends on nothing that moves.
def read() -> IO(M.Read):
  do IO<M.Read>:
    t : Maybe<&2, String> <- F.read(toml())
    return M.parse(F.text_of(t))

# the lines a run printed, or none when it failed, so a program's complaint on
# stderr is never mistaken for an answer
def answered(ok: Bool, +text: String) -> List<&2, String>:
  match ok:
    case True{}:
      Args.nonempty(String.lines(text))
    case False{}:
      []

# every package hash written anywhere in the lock. Grepping the file rather than
# parsing it means the lock can change format without changing this.
def locked() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["grep", "-ohE", "0x[0-9a-f]{32}", lock()])
    return D.uniq(Sort.sort(answered(R.ok(out), R.text(out))))

# what the lock amounts to
def lock.note(+hs: List<&2, String>) -> Note:
  Note{List.is_empty(&2, String, hs),
    lock() ++ ": " ++ plural(List.length(&2, String, hs), "package", "packages") ++
    Bool.pick(String, List.is_empty(&2, String, hs),
      " (unreadable, or it names none)", "")}

# the packages BEND_LIB holds, by the directory names under it
def present(+lib: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["ls", lib])
    return answered(R.ok(out), R.text(out))

# BEND_LIB judged against the lock: every package the lock names has to be on
# disk, because bend resolves a hub import during the check and a sandbox has
# no network to fall back on
def lib.said(all: Bool, +lib: String, +n: Nat, gone: List<&2, String>) -> Note:
  match all:
    case True{}:
      Note{False{}, "BEND_LIB: " ++ lib ++ ", all " ++
        plural(n, "locked package", "locked packages") ++ " present"}
    case False{}:
      Note{True{}, "BEND_LIB: " ++ lib ++ " lacks " ++ String.join(gone, " ") ++
        "; run ez fetch"}

# the verdict, once what is wanted and what is there are both known
def lib.judge(+lib: String, +want: List<&2, String>, have: List<&2, String>) -> Note:
  +gone = D.missing(want, have)
  lib.said(List.is_empty(&2, String, gone), lib,
    List.length(&2, String, want), gone)

# where the packages this build resolves against live. It is what ez itself
# passes to every bend it starts, so an unset BEND_LIB is not a finding: the
# default is `.ez/lib` beside the project, and what matters is what is in it.
def lib(want: List<&2, String>) -> IO(Note):
  do IO<Note>:
    +at : String <- Env.lib()
    have : List<&2, String> <- present(at)
    return lib.judge(at, want, have)

# every `import 0x...` line in the repo. Base has no readdir, so this is grep,
# and the exclusions keep the vendored copies under .ez out of the answer.
def imports() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["grep", "-rh", "--include=*.bend",
      "--exclude-dir=.ez", "--exclude-dir=.gate", "--exclude-dir=.git",
      "-e", "^import 0x", "."])
    return answered(R.ok(out), R.text(out))

# what the ledger and the source agree, or do not, about the hashes
def drift.said(none: Bool, +n: Nat, lines: List<&2, String>) -> Note:
  match none:
    case True{}:
      Note{False{}, "imports: " ++ plural(n, "package", "packages") ++
        " imported, every one named in ez.toml"}
    case False{}:
      Note{True{}, String.join(lines, "\n")}

# the drift report, and how many packages the source imports at all
def drift.go(+ls: List<&2, String>, r: M.Read) -> Note:
  +bad = D.report(ls, r)
  drift.said(List.is_empty(&2, String, bad),
    List.length(&2, String, D.imported(ls)), bad)

# the most valuable check ez has: the hashes in ez.toml against the `0x` hashes
# the source actually imports. ez reports the disagreement and never rewrites
# the source, so this is where a disagreement is said.
def drift(r: M.Read) -> IO(Note):
  do IO<Note>:
    ls : List<&2, String> <- imports()
    return drift.go(ls, r)

# whether a note is a problem
def note.wrong(n: Note) -> Bool:
  Note{w, _l} = n
  w

# what a note prints
def note.line(n: Note) -> String:
  Note{_w, l} = n
  l

# whether anything found was a problem
def wrong(ns: List<&2, Note>) -> Bool:
  match ns:
    case []:
      False{}
    case h <> t:
      Bool.or(note.wrong(h), wrong(t))

# the report, a note a line
def text(ns: List<&2, Note>) -> String:
  match ns:
    case []:
      ""
    case h <> t:
      note.line(h) ++ "\n" ++ text(t)

# a problem must fail the command, or a script around it learns nothing
def say.exit(ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "")

# everything found, printed, and the exit status it implies
def say(+ns: List<&2, Note>) -> IO(Unit):
  do IO<Unit>:
    IO.write(text(ns))
    say.exit(Bool.not(wrong(ns)))

# `ez doctor`: the toolchain and the project, reported on
def run() -> IO(Unit):
  do IO<Unit>:
    nbend : Note <- probe("bend")
    ncc : Note <- cc()
    ngit : Note <- probe("git")
    ncurl : Note <- probe("curl")
    +r : M.Read <- read()
    +hs : List<&2, String> <- locked()
    nlib : Note <- lib(hs)
    ndrift : Note <- drift(r)
    say([nbend, ncc, ngit, ncurl, toml.note(r), lock.note(hs), nlib, ndrift])
