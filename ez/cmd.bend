# ez/cmd: what each subcommand does. Everything that touches the network or the
# file system goes through one process effect, because bend links no TLS and
# Base has neither mkdir nor readdir.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../lock/run.bend as Run
import ../lock/world.bend as W
import ../lock/restore.bend as Restore
import ../git/git.bend as Git
import ../pub/pub.bend as Pub
import ./args.bend as Args
import ./env.bend as Env
import ./cap.bend as Cap
import ./target.bend as Tgt
import ../manifest/ignore.bend as Ig
import ./named.bend as Named
import ../ez/say.bend as Say
import ../init/run.bend as InitRun
import ../remove/run.bend as RemoveRun

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the ledger on disk, parsed
def load() -> IO(M.Read):
  do IO<M.Read>:
    t : Maybe<&2, String> <- F.read(toml())
    return M.parse(F.text_of(t))

# the ledger a command that edits it reads: what the file holds, parsed, or a
# refusal when there is no file. Only `ez init` makes a ledger; `ez add`,
# `ez remove` and `ez lock` read one, and one that is missing is not an empty
# one to write back.
def ledger.of(got: Maybe<&2, String>, +cmd: String) -> M.Read:
  match got:
    case None{}:
      M.Bad{"no " ++ toml() ++ " here; ez " ++ cmd ++
        " works on a project's ledger, and ez init makes one"}
    case Some{text}:
      M.parse(text)

# the ledger on disk, for a command that edits it
def load.edit(+cmd: String) -> IO(M.Read):
  do IO<M.Read>:
    t : Maybe<&2, String> <- F.read(toml())
    return ledger.of(t, cmd)

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

# the lock's path, which is fixed
def lockfile() -> String:
  "ez.lock.toml"

# `ez lock`, plain or `--upgrade`, is the planner's
# (lock/plan.bend, lock/up.bend): a plain lock copies every pin as the ledger
# has it, refuses one it would have to fill, and never writes ez.toml; an
# upgrade moves the selected pins, writes ez.toml once, `.gitignore`, the
# rewritten imports and the lock in one plan. Either writes nothing when it
# refuses, and a missing ledger is refused. `--package` is only a filter on an
# upgrade.
def lock.go(ok: Bool, up: Bool, +name: String) -> IO(Unit):
  match ok:
    case True{}:
      Run.run(W.Args{up, name})
    case False{}:
      IO.die(Unit, 1, "ez: --package needs --upgrade")

# `ez lock` and `ez lock --upgrade [--package NAME]`
def lock(+up: Bool, +name: String) -> IO(Unit):
  lock.go(Bool.or(up, String.is_empty(name)), up, name)

# BEND_LIB filled from the lock, with nothing re-resolved
def fetch() -> IO(Unit):
  Restore.restore(lockfile())

# `ez init [name] [entry.bend]`: a new project, planned by init/plan.bend
def init(+asked: String, +file: String) -> IO(Unit):
  InitRun.run(asked, file)

# a vendoring's answer as a ledger entry, under the name `ez/named.bend` gave
# it.
#
# `root` and the NAR hash are in the ledger because `ez lock` needs them and a
# clone, which never sees .ez/origins.toml, would otherwise have to guess. They
# come straight off the vendoring that computed them: it weighed the tree for
# the NAR hash and worked the root out from where the entry sat, so asking the
# cache it just wrote would be reading back our own answer.
def add.dep.go(
  name: String,
  hash: String,
  url: String,
  rev: String,
  at: String,
  tag: String,
  root: String,
  nar: String
) -> M.Dep:
  M.Dep{name, hash, at, M.Git{url, rev, tag, root, nar, False{}}}

# what a vendoring answered, as the ledger records it
def add.dep(name: String, got: Git.Got) -> M.Dep:
  Git.Got{h, u, v, e, t, r, n, _p} = got
  add.dep.go(name, h, u, v, e, t, r, n)

# the `[package] name` the vendored checkout gave itself, "" for none
def add.pkg(got: Git.Got) -> String:
  Git.Got{_h, _u, _v, _e, _t, _r, _n, p} = got
  p

# the dependencies of a ledger that was read
def deps.of(manifest: M.Manifest) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, ds, _ts} = manifest
  ds

# a write that did not happen is a failure
def allowlist.wrote(ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: .gitignore could not be written")

# the ignore file, written only when the allowlist the ledger calls for is
# not the one it already has, so a command that changed nothing vendored
# leaves the file as it found it, byte for byte
def allowlist.put(same: Bool, +next: String) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        ok : Bool <- F.write(".gitignore", next)
        allowlist.wrote(ok)

# the ignore file's text against the one the ledger calls for
def allowlist.text(ds: List<&2, M.Dep>, +text: String) -> IO(Unit):
  +next = Ig.sync(ds, text)
  allowlist.put(String.eq(next, text), next)

# the gitignore allowlist, derived from the ledger's dependencies: exactly
# the hashes marked `vendor = true`, with every other line kept. `ez add`
# calls this with the ledger it just wrote; `ez remove` and `ez lock --upgrade`
# plan the same `Ig.sync`. A missing file reads as empty, and stays missing
# when the ledger vendors nothing.
def allowlist(ds: List<&2, M.Dep>) -> IO(Unit):
  do IO<Unit>:
    g : Maybe<&2, String> <- F.read(".gitignore")
    allowlist.text(ds, F.text_of(g))

# an edited ledger written, then the gitignore allowlist derived from it
def edit.write(+next: M.Manifest) -> IO(Unit):
  do IO<Unit>:
    wrote : Bool <- F.write(toml(), Rend.show(next))
    allowlist(deps.of(next))
    report.exit(wrote)

# a name the ledger can take, written into it with the dependency. A
# dependency added again keeps the `vendor = true` its entry already had.
def add.take(ok: Bool, why: String, manifest: M.Manifest, name: String, got: Git.Got) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, why)
    case True{}:
      edit.write(Rend.add.keep(manifest, add.dep(name, got)))

# the vendoring's answer named, by `Named.name`, and refused when the ledger
# gives that name to another source
def add.named(
  +manifest: M.Manifest,
  +got: Git.Got,
  +fresh: String,
  +url: String,
  +rename: String
) -> IO(Unit):
  +name = Named.as(deps.of(manifest), url, rename, add.pkg(got), fresh)
  +why = Named.why.as(deps.of(manifest), name, url, rename)
  add.take(String.is_empty(why), why, manifest, name, got)

# a `--rename` that is no key is refused before anything is fetched
def add.fetch(
  ok: Bool,
  +manifest: M.Manifest,
  +fresh: String,
  +url: String,
  +ref: String,
  +entry: String,
  +rename: String
) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, Named.why.as(deps.of(manifest), rename, url, rename))
    case True{}:
      do IO<Unit>:
        lib : String <- Env.lib()
        g : Git.Got <- Git.vendor(lib, url, ref, entry)
        add.named(manifest, g, fresh, url, rename)

# a git dependency vendored, then recorded in the ledger. The name can turn on
# the checkout's own ez.toml, so it is decided once the checkout is read; a
# refusal then leaves the ledger as it was, and only the cache under BEND_LIB
# holds the tree. A ledger that does not parse is refused before anything is
# fetched. The vendoring comes before the write: a ledger naming a package
# that is not on disk is worse than no entry at all.
def add.go(
  ledger: M.Read,
  fresh: String,
  +url: String,
  +ref: String,
  +entry: String,
  +rename: String
) -> IO(Unit):
  match ledger:
    case M.Bad{why}:
      refuse(M.Bad{why})
    case M.Good{manifest}:
      add.fetch(Named.renamed.ok(rename), manifest, fresh, url, ref, entry, rename)

# a path, with `~` expanded the way `ez tool run` expands it. A relative path
# is kept as it was given, relative to the project, so the ledger reads the
# same on any clone; git is handed it anchored (`Git.anchored`).
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

# `ez add <target> [rev|tag|branch] [entry.bend] [--rename NAME]`. The target is an
# `owner/repo`, a git url, or a path, the same shapes `ez tool run` takes.
# A missing ref is resolved, and a missing entry is read from the checkout.
def add(+target: String, +ref: String, +entry: String, +rename: String) -> IO(Unit):
  +place = Tgt.classify(target)
  do IO<Unit>:
    +url : String <- add.url(place)
    +got : String <- add.ref.at(Bool.not(String.is_empty(ref)), url, ref)
    r : M.Read <- load.edit("add")
    +from : String <- Git.anchored(url)
    add.go(r, Named.called(place, from), url, got, entry, rename)

# `ez remove <name>`, planned by remove/plan.bend
def remove(+name: String) -> IO(Unit):
  RemoveRun.run(name)
