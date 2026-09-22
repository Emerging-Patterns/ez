# ez/upgrade: `ez lock --upgrade`. The lock is rewritten either way. A git
# dependency with a tag is re-resolved to that tag; one with only a commit
# fast-forwards to the default branch tip when the pin is an ancestor of it.
# A hub dependency is left, because the hash is the pin. `ez fetch` still
# fills BEND_LIB for everything else. A dependency with `vendor = true` is
# the exception: its tree is committed under `.ez/lib/<hash>` and named in
# the gitignore allowlist, so a move lays the new tree there and rewrites
# the line. An import that names the old hash is rewritten to the new one.
import Base
import ../io/file.bend as F
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/upgrade.bend as U
import ../git/git.bend as Git
import ../hub/hub.bend as Web
import ../lock/lock.bend as L
import ./args.bend as Args

# what one dependency became. `old` is the hash the allowlist must drop, ""
# when the tree is not committed or the hash did not change. `prev` is the
# content hash an import must stop naming, "" when that hash did not change.
type Done is Data:
  Done{dep: M.Dep, old: String, new: String, prev: String, moved: Bool}

# the whole ledger after the walk. `swaps` rename committed trees. `edits`
# rename the hashes import lines carry.
type Out is Data:
  Out{deps: List<&2, M.Dep>, swaps: List<&2, U.Swap>, edits: List<&2, U.Swap>, moved: Bool}

# where a committed tree is laid. The allowlist names this directory, not
# whatever BEND_LIB a shell happened to export.
def lib() -> String:
  ".ez/lib"

# the ignore file the allowlist lives in
def ignore() -> String:
  ".gitignore"

# a directory the ancestry clone may use, under the ignored half of `.ez/`
def work() -> String:
  ".ez/lib/.work-up"

# one dependency left as it was
def stay(d: M.Dep) -> Done:
  Done{d, "", "", "", False{}}

# a moved pin. `old` is the hash the allowlist must drop, "" when the tree
# is not committed or the hash did not change. `prev` is the content hash
# the imports named, "" when that hash did not change.
def moved(d: M.Dep, +old: String, +new: String, +prev: String) -> Done:
  Done{d, old, new, prev, True{}}

# the hash to drop from the allowlist, or "" when there is nothing to drop
def swap.hash(same: Bool, +old: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      old

# a committed tree whose hash changed is an allowlist edit
def swap.of(vend: Bool, +old: String, +new: String) -> String:
  match vend:
    case False{}:
      ""
    case True{}:
      swap.hash(String.eq(old, new), old)

# a hub pin named with `--package` is reported and left. An unselected
# dependency is left quietly. Hold on a selected dependency is a hub pin:
# a selected git pin is Follow or Forward instead.
def hold.say(sel: Bool, +d: M.Dep) -> IO(Done):
  match sel:
    case False{}:
      IO.pure(Done, stay(d))
    case True{}:
      do IO<Done>:
        IO.print(M.dep.name(d) ++ ": pinned by its hash")
        return stay(d)

# Hold is an unselected dependency, or a selected one that has no repo
def hold(+only: String, +d: M.Dep) -> IO(Done):
  hold.say(U.chosen(only, M.dep.name(d)), d)

# the hub's answer, which fails the upgrade only when a body arrived and
# did not hash to the name we asked for
def hub.miss(bad: Bool, +name: String, +hash: String) -> IO(Unit):
  match bad:
    case True{}:
      IO.die(Unit, 1, "ez: " ++ name ++ ": hub digest does not match " ++ hash)
    case False{}:
      IO.pure(Unit, Unit{})

# the hub's answer
def hub.got(+name: String, +hash: String, g: Web.Got) -> IO(Unit):
  match g:
    case Web.Have{_body}:
      IO.pure(Unit, Unit{})
    case Web.Miss{why}:
      hub.miss(U.hub.bad(why), name, hash)

# the manifest at the hash git just computed, when the hub has one
def hub.check(+hub: String, +name: String, +hash: String) -> IO(Unit):
  do IO<Unit>:
    g : Web.Got <- Web.fetch(L.url_of(hub, hash, "manifest"), L.want(hash))
    hub.got(name, hash, g)

# a tag that moved off the pin's history, or a branch tip that does not
# descend from a rev-only pin
def off.why(+name: String, +tag: String, +pin: String, +tip: String) -> String:
  Bool.pick(String, String.is_empty(tag),
    "ez: " ++ name ++ ": " ++ pin ++ " is not an ancestor of " ++ tip,
    "ez: " ++ name ++ ": tag " ++ tag ++ " moved off " ++ pin)

# the same commit, whose tree no longer hashes to the pin
def drift.why(+name: String, +rev: String, +old: String, +new: String) -> String:
  "ez: " ++ name ++ ": hash drifted at " ++ rev ++ " (" ++ old ++ " vs " ++ new ++ ")"

# the branch a rev-only pin followed, said when there is one
def branch.of(+b: String) -> String:
  Bool.pick(String, String.is_empty(b), "", " (" ++ b ++ ")")

# a pin that moved
def say.move(+name: String, +old: String, +new: String, +branch: String) -> IO(Unit):
  IO.print(name ++ ": " ++ old ++ " -> " ++ new ++ branch.of(branch))

# a committed tree laid out under its new hash
def say.tree(+name: String, +hash: String) -> IO(Unit):
  IO.print(name ++ ": vendored .ez/lib/" ++ hash)

# the vendored line only when a tree was committed under a new hash
def say.tree.go(empty: Bool, +name: String, +hash: String) -> IO(Unit):
  match empty:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      say.tree(name, hash)

# a content hash that changed, said as the import rewrite. A pin whose
# tree still hashes the same has no import to rewrite.
def say.imports(same: Bool, +name: String, +old: String, +new: String) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print(name ++ ": imports " ++ old ++ " -> " ++ new)

# a pin that was already where the remote points
def say.keep(+name: String, +rev: String) -> IO(Unit):
  IO.print(name ++ ": unchanged " ++ rev)

# the checkout weighed, then judged against the pin it was meant to confirm
def confirmed(ok: Bool, +hub: String, +d: M.Dep, +hash: String, +rev: String) -> IO(Done):
  match ok:
    case False{}:
      IO.die(Done, 1, drift.why(M.dep.name(d), rev, M.dep.hash(d), hash))
    case True{}:
      do IO<Done>:
        hub.check(hub, M.dep.name(d), hash)
        say.keep(M.dep.name(d), rev)
        return stay(d)

# a checkout of the commit the ledger already pins
def confirm(+hub: String, +d: M.Dep, g: Git.Got) -> IO(Done):
  Git.Got{+hash, _url, +rev, _entry, _tag, +root, +nar} = g
  +src = M.source.dep(d)
  confirmed(U.agree(M.dep.hash(d), hash, M.source.nar(src), nar,
    M.source.root(src), root), hub, d, hash, rev)

# the new pin, the allowlist edit, and what a person is told
def advanced(+hub: String, +d: M.Dep, g: Git.Got, +branch: String) -> IO(Done):
  Git.Got{+hash, _url, +rev, _entry, _tag, +root, +nar} = g
  +src = M.source.dep(d)
  +old = M.dep.hash(d)
  +drop = swap.of(M.source.vendor(src), old, hash)
  +prev = swap.hash(String.eq(old, hash), old)
  do IO<Done>:
    hub.check(hub, M.dep.name(d), hash)
    say.move(M.dep.name(d), M.source.rev(src), rev, branch)
    say.imports(String.is_empty(prev), M.dep.name(d), old, hash)
    say.tree.go(String.is_empty(drop), M.dep.name(d), hash)
    return moved(U.retarget(d, rev, hash, root, nar), drop, hash, prev)

# the word Off quotes: a branch name when we have one, otherwise the commit
def tip.of(+branch: String, +tip: String) -> String:
  Bool.pick(String, String.is_empty(branch), tip, branch)

# the verdict, once the remote has been asked and the ancestry read.
# `branch` is the default-branch name for a rev-only pin and "" for a tag,
# which is what the move line puts in parentheses. Off quotes the branch
# when there is one and the tip commit otherwise.
def judged(v: U.Verdict, +lib: String, +hub: String, +d: M.Dep, +url: String,
  +entry: String, +pin: String, +tip: String, +branch: String) -> IO(Done):
  match v:
    case U.Keep{}:
      do IO<Done>:
        g : Git.Got <- Git.vendor.at(lib, url,
          Git.Ref{pin, M.source.tag(M.source.dep(d))}, entry)
        confirm(hub, d, g)
    case U.Drift{}:
      IO.die(Done, 1, drift.why(M.dep.name(d), pin, M.dep.hash(d), M.dep.hash(d)))
    case U.Off{}:
      IO.die(Done, 1, off.why(M.dep.name(d), M.source.tag(M.source.dep(d)),
        pin, tip.of(branch, tip)))
    case U.Advance{+rev, tag}:
      do IO<Done>:
        g : Git.Got <- Git.vendor.at(lib, url, Git.Ref{rev, tag}, entry)
        advanced(hub, d, g, branch)

# ancestry's answer turned into a verdict. `agree` is true here because the
# tree has not been weighed yet; a same commit is weighed in Keep, and a
# disagreement there is the drift.
def resolved(+lib: String, +hub: String, +d: M.Dep, +url: String, +entry: String,
  +pin: String, +tip: String, +tag: String, +branch: String, onward: Bool) -> IO(Done):
  judged(U.judge(String.eq(pin, tip), onward, True{}, tip, tag),
    lib, hub, d, url, entry, pin, tip, branch)

# ancestry, then the verdict. The same commit skips the clone.
def ask(+lib: String, +hub: String, d: M.Dep, +url: String, +entry: String,
  +pin: String, +tip: String, +tag: String, +branch: String) -> IO(Done):
  do IO<Done>:
    +on : Bool <- Git.descendant.at(work(), url, pin, tip)
    resolved(lib, hub, d, url, entry, pin, tip, tag, branch, on)

# a recorded tag, re-resolved
def follow.got(+lib: String, +hub: String, +d: M.Dep, +src: M.Source, r: Git.Ref) -> IO(Done):
  Git.Ref{+rev, tag} = r
  ask(lib, hub, d, M.source.url(src), M.dep.entry(d), M.source.rev(src),
    rev, tag, "")

def follow(+lib: String, +hub: String, +d: M.Dep, +ref: String) -> IO(Done):
  +src = M.source.dep(d)
  do IO<Done>:
    r : Git.Ref <- Git.resolve(M.source.url(src), ref)
    follow.got(lib, hub, d, src, r)

# a rev-only pin, against the default branch tip
def forward.got(+lib: String, +hub: String, +d: M.Dep, t: Git.Tip) -> IO(Done):
  Git.Tip{+rev, +branch} = t
  +src = M.source.dep(d)
  ask(lib, hub, d, M.source.url(src), M.dep.entry(d), M.source.rev(src),
    rev, "", branch)

# a rev-only pin
def forward(+lib: String, +hub: String, +d: M.Dep) -> IO(Done):
  do IO<Done>:
    t : Git.Tip <- Git.remote(M.source.url(M.source.dep(d)))
    forward.got(lib, hub, d, t)

# one dependency
def one(a: U.Aim, +lib: String, +hub: String, +only: String, d: M.Dep) -> IO(Done):
  match a:
    case U.Hold{}:
      hold(only, d)
    case U.Follow{ref}:
      follow(lib, hub, d, ref)
    case U.Forward{}:
      forward(lib, hub, d)

# an allowlist edit, kept only when there is a hash to drop
def swaps.put(empty: Bool, +old: String, +new: String, rest: List<&2, U.Swap>) -> List<&2, U.Swap>:
  match empty:
    case True{}:
      rest
    case False{}:
      U.Swap{old, new} <> rest

# either side moved
def either(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

# one dependency in front of the rest of the ledger
def join(a: Done, b: Out) -> Out:
  Done{d, +old, +new, +prev, moved} = a
  Out{ds, ss, es, any} = b
  Out{d <> ds, swaps.put(String.is_empty(old), old, new, ss),
    swaps.put(String.is_empty(prev), prev, new, es), either(moved, any)}

# every dependency, in the order the ledger wrote them
def walk(+lib: String, +hub: String, +only: String, ds: List<&2, M.Dep>) -> IO(Out):
  match ds:
    case []:
      IO.pure(Out, Out{[], [], [], False{}})
    case +h <> t:
      do IO<Out>:
        +a : Done <- one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)),
          lib, hub, only, h)
        +b : Out <- walk(lib, hub, only, t)
        return join(a, b)

# a write that did not happen is a failure
def wrote(ok: Bool, +at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# the ledger, rewritten only when a pin moved, so an upgrade that changed
# nothing does not reformat the file
def write.toml(moved: Bool, +name: String, +entry: String, +bin: String,
  ds: List<&2, M.Dep>, ts: List<&2, M.Tool>) -> IO(Unit):
  match moved:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        ok : Bool <- F.write("ez.toml",
          Rend.show(M.Manifest{name, entry, bin, ds, ts}))
        wrote(ok, "ez.toml")

# the ignore file with every committed hash that moved
def write.ignore.go(empty: Bool, ss: List<&2, U.Swap>) -> IO(Unit):
  match empty:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        g : Maybe<&2, String> <- F.read(ignore())
        ok : Bool <- F.write(ignore(), U.reallow.many(ss, F.text_of(g)))
        wrote(ok, ignore())

def write.ignore(+ss: List<&2, U.Swap>) -> IO(Unit):
  write.ignore.go(List.is_empty(&2, U.Swap, ss), ss)

# a listing that did not happen is a failure
def sources.got(ok: Bool, +text: String) -> IO(List<&2, String>):
  match ok:
    case False{}:
      IO.die(List<&2, String>, 1, "ez: could not list sources")
    case True{}:
      IO.pure(List<&2, String>, Args.nonempty(String.lines(text)))

# every Bend source of the project. Vendored trees and the gate's shadow
# live under .ez, and a checkout's .git is not source, so neither is rewritten.
def sources() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["find", ".", "-name", "*.bend",
      "-not", "-path", "*/.ez/*", "-not", "-path", "*/.git/*"])
    sources.got(R.ok(out), R.text(out))

# a source left untouched when the rewrite changes nothing
def rewrite.put(same: Bool, +at: String, +next: String) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        ok : Bool <- F.write(at, next)
        wrote(ok, at)

def rewrite.body(+at: String, +text: String, +next: String) -> IO(Unit):
  rewrite.put(String.eq(text, next), at, next)

# a source that could not be read is a failure
def rewrite.open(m: Maybe<&2, String>, +at: String, ss: List<&2, U.Swap>) -> IO(Unit):
  match m:
    case None{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be read")
    case Some{+text}:
      rewrite.body(at, text, U.reimport.many(ss, text))

# one source, with every hash that moved rewritten
def rewrite.file(+at: String, ss: List<&2, U.Swap>) -> IO(Unit):
  do IO<Unit>:
    g : Maybe<&2, String> <- F.read(at)
    rewrite.open(g, at, ss)

# every source
def rewrite.all(ps: List<&2, String>, +ss: List<&2, U.Swap>) -> IO(Unit):
  match ps:
    case []:
      IO.pure(Unit, Unit{})
    case +h <> t:
      do IO<Unit>:
        rewrite.file(h, ss)
        rewrite.all(t, ss)

# the project's imports, rewritten when a hash moved
def write.imports.go(empty: Bool, ss: List<&2, U.Swap>) -> IO(Unit):
  match empty:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        ps : List<&2, String> <- sources()
        rewrite.all(ps, ss)

def write.imports(+ss: List<&2, U.Swap>) -> IO(Unit):
  write.imports.go(List.is_empty(&2, U.Swap, ss), ss)

# one old tree, gone. The new one is already laid out beside it.
def drop.one(+hash: String) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", lib() ++ "/" ++ hash])
    return Unit{}

# every old committed tree
def drop(ss: List<&2, U.Swap>) -> IO(Unit):
  match ss:
    case []:
      IO.pure(Unit, Unit{})
    case U.Swap{+old, _new} <> t:
      do IO<Unit>:
        drop.one(old)
        drop(t)

# pins rewritten, then the allowlist, then the imports, then the old trees.
# The lock is the caller's to write, from the ledger this just wrote.
def go.out(+name: String, +entry: String, +bin: String, ts: List<&2, M.Tool>,
  o: Out) -> IO(Unit):
  Out{+deps, +swaps, +edits, moved} = o
  do IO<Unit>:
    write.toml(moved, name, entry, bin, deps, ts)
    write.ignore(swaps)
    write.imports(edits)
    drop(swaps)

def go(+name: String, +entry: String, +bin: String, ds: List<&2, M.Dep>,
  ts: List<&2, M.Tool>, +only: String) -> IO(Unit):
  do IO<Unit>:
    +hub : String <- L.hub()
    o : Out <- walk(lib(), hub, only, ds)
    go.out(name, entry, bin, ts, o)

# `--package` has to name a dependency or a pinned CLI
def read.known(ok: Bool, +name: String, +entry: String, +bin: String,
  ds: List<&2, M.Dep>, ts: List<&2, M.Tool>, +only: String) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, "ez: no dependency or tool named " ++ only)
    case True{}:
      go(name, entry, bin, ds, ts, only)

# a ledger that parsed
def read.good(m: M.Manifest, +only: String) -> IO(Unit):
  M.Manifest{+name, +entry, +bin, +ds, +ts} = m
  read.known(either(U.known(only, ds), M.tool.known(only, ts)), name, entry,
    bin, ds, ts, only)

# the ledger on disk, or the reason it was not one
def read.go(r: M.Read, +only: String) -> IO(Unit):
  match r:
    case M.Bad{why}:
      IO.die(Unit, 1, "ez: " ++ why)
    case M.Good{m}:
      read.good(m, only)

# `ez lock --upgrade`, for every dependency or for the one named
def run(+only: String) -> IO(Unit):
  do IO<Unit>:
    t : Maybe<&2, String> <- F.read("ez.toml")
    read.go(M.parse(F.text_of(t)), only)
