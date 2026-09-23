# ez/cmd: what each subcommand does. Everything that touches the network or the
# file system goes through one process effect, because bend links no TLS and
# Base has neither mkdir nor readdir.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../lock/lock.bend as Lock
import ../lock/restore.bend as Restore
import ../git/git.bend as Git
import ../pub/pub.bend as Pub
import ../pkg/path.bend as P
import ./args.bend as Args
import ./env.bend as Env
import ./cap.bend as Cap
import ./target.bend as Tgt
import ./upgrade.bend as Up
import ./pin.bend as Pin
import ./sorted.bend as Sorted
import ../ez/say.bend as Say

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
def entry.or(+file: String) -> String:
  Bool.pick(String, String.is_empty(file), "main.bend", file)

# the name a ledger gives the package, or `app` when there is no ledger to ask
def named(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{_why}:
      "app"
    case M.Good{m}:
      M.Manifest{n, _e, _b, _h, _ds, _ts} = m
      n

# the entry file of a ledger that was read
def entry(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{_why}:
      "main.bend"
    case M.Good{m}:
      M.Manifest{_n, e, _b, _h, _ds, _ts} = m
      entry.or(e)

# a ledger that would not parse stops the command before it does damage
def refuse(ledger: M.Read) -> IO(Unit):
  IO.die(Unit, 1, "ez: " ++ M.show(ledger))

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
#
# It is matched as a whole line, because that is the shape of the thing being
# claimed: bend prints it as `Error: no main to run` and nothing else. Asked as
# a substring of the whole output, the same words appearing anywhere — inside
# some other error's text, or in a source line bend echoed back while
# reporting on it — would answer yes and mean nothing, and a failing check
# would read as a passing one. Two other line-shaped facts in this tree were
# being asked of whole files the same way, and one of them silently dropped a
# test before it was caught.
def no.main(+line: String) -> Bool:
  String.eq(line, "Error: no main to run")

# whether any line of the output is that one. The rest of the walk is bound
# before the `Bool.or` rather than written under it: `Bool.or` is an ordinary
# function and reduces both sides, so a recursive call sitting inside one is
# not a branch the condition can decline. Bound first it is a plain fold over
# a handful of lines, which is what the rest of this tree does too.
def said.no.main(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      +rest = said.no.main(t)
      Bool.or(no.main(h), rest)

def check.passed(+out: String) -> Bool:
  Bool.or(R.ok(out), said.no.main(String.lines(R.text(out))))

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
def build(+out: String) -> IO(Unit):
  do IO<Unit>:
    +r : M.Read <- load()
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +g : String <- Cap.gb()
    +bin : String <- Cap.run(cap, ["bend", entry(r), "-o",
      build.out(out, named(r))])
    report.capped(Cap.why(bin, g), bin)

# the entry run, which checks it first
def run(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +out : String <- Env.exec(List.append(&2, String, ["bend", entry(r)], as))
    report(out)

# `ez publish`: the entry the ledger names, sent to the hub the way `ez build`
# and `ez check` build and check that same entry. The `0x` name reported is the
# one `pkg/pkg.bend` computed from the file set; what `bend --publish` printed
# is only checked against it. `pub/pub.bend` holds the whole of it, laws and
# all, and is handed the project's BEND_LIB the way `git/git.bend` is handed it
# for a vendoring.
def publish() -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +at : String <- IO.pure(String, entry(r))
    lib : String <- Env.lib()
    Pub.publish(lib, at)

# a listed path the lock starts from: any but the committed trees under
# `.ez/`, which are packages and not the project's own sources
def root.keep(+at: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.starts_with(at, ".ez/"), [], [at])

# every listed path the lock starts from
def roots.of(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case h <> t:
      List.append(&2, String, root.keep(h), roots.of(t))

# the lock's roots, from what `git ls-files` printed: blank lines dropped,
# `.ez/` dropped, and the rest in order, so the walk starts from the same
# list on every machine
def tracked(ls: List<&2, String>) -> List<&2, String>:
  Sorted.sort(roots.of(Args.nonempty(ls)))

# a listing that failed is not an empty project. Outside a git repository
# there is no committed tree to lock, and a lock of whatever happened to be
# on disk is one a clone could not reproduce.
def sources.got(ok: Bool, +text: String) -> IO(List<&2, String>):
  match ok:
    case True{}:
      IO.pure(List<&2, String>, tracked(String.lines(text)))
    case False{}:
      IO.die(List<&2, String>, 1,
        "ez: ez lock reads the .bend files git tracks, and git could not list them: " ++
          String.trim(text))

# every .bend file git tracks under the current directory, for the lock's
# roots. Untracked files are not a clone's, so they are not the lock's.
def sources() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["git", "-c", "core.quotepath=off", "ls-files",
      "--", "*.bend"])
    sources.got(R.ok(out), R.text(out))

# the lock's path, which is fixed
def lockfile() -> String:
  "ez.lock.toml"

# the lock, rewritten from every root in the tree
def lock.now() -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Say.resolving())
    srcs : List<&2, String> <- sources()
    text : String <- Lock.lock(srcs)
    wrote : Bool <- F.write(lockfile(), text)
    report.exit(wrote)

# `--package` is only a filter on an upgrade. A plain lock copies every pin
# as the ledger has it, and refuses one it would have to fill.
def lock.plain(bare: Bool, +_name: String) -> IO(Unit):
  match bare:
    case True{}:
      do IO<Unit>:
        Pin.need()
        lock.now()
    case False{}:
      IO.die(Unit, 1, "ez: --package needs --upgrade")

# `ez lock`, or `ez lock --upgrade` which re-pins git deps and tools first
# and then resolves. The lock is written from the ledger either way. A tool
# pin is recorded under `[tools.*]` and is not laid into BEND_LIB. A git
# dependency whose tree is not under BEND_LIB is fetched at its ledger rev by
# the lock itself, since its files are what the lock records; filling the rest
# of BEND_LIB stays `ez fetch`'s. A `vendor = true` dependency is laid out by
# the upgrade itself, because that tree is committed.
def lock.up(up: Bool, +name: String) -> IO(Unit):
  match up:
    case False{}:
      lock.plain(String.is_empty(name), name)
    case True{}:
      do IO<Unit>:
        Up.run(name)
        Pin.upgrade(name)
        lock.now()

# `ez lock` and `ez lock --upgrade [--package NAME]`
def lock(up: Bool, +name: String) -> IO(Unit):
  lock.up(up, name)

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
#
# `.ez/` is ignored as its contents rather than as a directory, and
# `.ez/lib` is let back in only to have its contents ignored again. That is
# what lets a `!.ez/lib/<hash>` line keep a vendored tree: git cannot
# re-include a file under a directory it has excluded, so under a bare
# `.ez/` every such line would be inert.
def init.rules(+name: String) -> List<&2, String>:
  [".ez/*", "!.ez/lib", ".ez/lib/*", build.named(name)]

# one step of a scan that is looking for one hit, with the head's answer in
# hand. `Bool.or` is an ordinary function and reduces both of its sides, so a
# scan written with it reads the whole list even when the first line answers.
# The rest of the scan arrives as a thunk and only the arm that wants it
# applies it.
def stated.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a file already states this rule, on a line of its own. A rule buried
# in a longer line is not the rule, so the comparison is against whole lines.
def stated(ls: List<&2, String>, +rule: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      stated.step(String.eq(String.trim(h), rule), _u => stated(t, rule))

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

# nothing to add means nothing written, so an `ez init` in a directory whose
# ignore file already has the rules leaves it exactly as it found it
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

# the entry of a new project: a program that checks and runs
def init.stub() -> String:
  "import Base\n\ndef main() -> IO(Unit):\n  IO.print(\"hello\")\n"

# the entry written, with every directory above it made first. Base has no
# mkdir, so this is the same coreutils call every other write that needs a
# directory already uses.
def init.entry.put(+at: String) -> IO(Bool):
  do IO<Bool>:
    _mk : String <- R.exec(["mkdir", "-p", P.dir(at)])
    F.write(at, init.stub())

# an entry that is already there is left alone, so `ez init` does not
# overwrite the program
def init.entry.go(got: Maybe<&2, String>, +at: String) -> IO(Bool):
  match got:
    case Some{_s}:
      IO.pure(Bool, True{})
    case None{}:
      init.entry.put(at)

# the project's entry file, made when the directory does not already hold one
def init.entry(+at: String) -> IO(Bool):
  do IO<Bool>:
    g : Maybe<&2, String> <- F.read(at)
    init.entry.go(g, at)

# the ledger a new project starts from, or nothing when there already is one.
# A ledger on disk holds dependencies, tools and a `bin` that a fresh one would
# lose, so `ez init` writes over none of it, whatever the file holds.
def init.plan(got: Maybe<&2, String>, +name: String, +at: String) -> Maybe<&2, String>:
  match got:
    case Some{_s}:
      None{}
    case None{}:
      Some{Rend.show(M.Manifest{name, at, "", "", [], []})}

# the ledger written, then the ignore rules for what ez will generate beside
# it, and the entry itself when the directory does not already hold one. A
# project that already has a ledger is refused before anything is written.
def init.go(plan: Maybe<&2, String>, +name: String, +at: String) -> IO(Unit):
  match plan:
    case None{}:
      IO.die(Unit, 1, "ez: " ++ toml() ++
        " already exists; ez init writes a new project and leaves it alone")
    case Some{text}:
      do IO<Unit>:
        wrote : Bool <- F.write(toml(), text)
        +kept : Bool <- init.ignore(name)
        +made : Bool <- init.entry(at)
        report.exit(Bool.and(wrote, Bool.and(kept, made)))

# a new project: a ledger naming this directory and its entry file, the
# ignore rules and the entry
def init(+asked: String, +file: String) -> IO(Unit):
  do IO<Unit>:
    +name : String <- IO.pure(String, init.name(asked))
    +at : String <- IO.pure(String, entry.or(file))
    got : Maybe<&2, String> <- F.read(toml())
    init.go(init.plan(got, name, at), name, at)

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
  +leaf = add.base(String.split(at, '/'))
  String.take(leaf, Nat.sub(String.length(leaf), 5n))

# a vendoring's answer as a ledger entry. The entry file is read twice, once
# for the name and once for itself, so it arrives through a parameter.
#
# `root` and the NAR hash are in the ledger because `ez lock` needs them and a
# clone, which never sees .ez/origins.toml, would otherwise have to guess. They
# come straight off the vendoring that computed them: it weighed the tree for
# the NAR hash and worked the root out from where the entry sat, so asking the
# cache it just wrote would be reading back our own answer.
def add.dep.go(hash: String, url: String, rev: String, +at: String, tag: String, root: String, nar: String) -> M.Dep:
  M.Dep{add.alias(at), hash, at, M.Git{url, rev, tag, root, nar, False{}}}

# what a vendoring answered, as the ledger records it
def add.dep(got: Git.Got) -> M.Dep:
  Git.Got{h, u, v, e, t, r, n} = got
  add.dep.go(h, u, v, e, t, r, n)

# the dependencies of a ledger that was read
def deps.of(manifest: M.Manifest) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, ds, _ts} = manifest
  ds

# an edited ledger written, then the gitignore allowlist derived from it
def edit.write(+next: M.Manifest) -> IO(Unit):
  do IO<Unit>:
    wrote : Bool <- F.write(toml(), Rend.show(next))
    Up.allowlist(deps.of(next))
    report.exit(wrote)

# the ledger with this dependency written into it. A dependency added again
# keeps the `vendor = true` its entry already had.
def add.write(ledger: M.Read, dep: M.Dep) -> IO(Unit):
  match ledger:
    case M.Bad{why}:
      refuse(M.Bad{why})
    case M.Good{m}:
      edit.write(Rend.add.keep(m, dep))

# a git dependency vendored, and then recorded in the ledger under its own
# name. The vendoring comes first: a ledger naming a package that is not on
# disk is worse than no entry at all.
def add.go(+url: String, +ref: String, +entry: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Env.lib()
    g : Git.Got <- Git.vendor(lib, url, ref, entry)
    r : M.Read <- load()
    add.write(r, add.dep(g))

# a path, with `~` expanded the way `ez tool run` expands it
def add.local(+path: String) -> IO(String):
  do IO<String>:
    +home : String <- Env.var("HOME", "")
    return Tgt.expand(home, path)

# the git url a target names
def add.url(place: Tgt.Place) -> IO(String):
  match place:
    case Tgt.Bad{why}:
      IO.die(String, 1, "ez: " ++ why)
    case Tgt.Local{path}:
      add.local(path)
    case Tgt.Remote{url, _slug}:
      IO.pure(String, url)

# a ref that was asked for, or the one `Git.default.ref` chooses: the greatest
# release tag, else the greatest pre-release, else the default branch
def add.ref.at(given: Bool, +url: String, +ref: String) -> IO(String):
  match given:
    case True{}:
      IO.pure(String, ref)
    case False{}:
      Git.default.ref(url)

# `ez add <target> [rev|tag|branch] [entry.bend]`. The target is an
# `owner/repo`, a git url, or a path, the same shapes `ez tool run` takes.
# A missing ref is resolved, and a missing entry is read from the checkout.
def add(+target: String, +ref: String, +entry: String) -> IO(Unit):
  do IO<Unit>:
    +url : String <- add.url(Tgt.classify(target))
    +got : String <- add.ref.at(Bool.not(String.is_empty(ref)), url, ref)
    add.go(url, got, entry)

# the ledger with a dependency dropped, and its allowlist line with it
def remove.write(ledger: M.Read, name: String) -> IO(Unit):
  match ledger:
    case M.Bad{why}:
      refuse(M.Bad{why})
    case M.Good{m}:
      edit.write(Rend.remove(m, name))

# `ez remove <name>`
def remove(+name: String) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    remove.write(r, name)
