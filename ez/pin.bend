# ez/pin: `ez lock` fills a `[tools.*]` pin, and `ez lock --upgrade` moves one.
# A tag is re-resolved to a commit and the NAR hash is filled, the way a git
# dependency is pinned. The checkout is weighed and removed. Nothing is laid
# under `.ez/lib`, and no import line is rewritten: a tool is not a package.
import Base
import ../io/file.bend as F
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/upgrade.bend as U
import ../git/git.bend as Git
import ../ez/say.bend as Say

# one tool after it was asked about
type Touched is Data:
  Touched{tool: M.Tool, moved: Bool}

# the tools after the walk
type Bunch is Data:
  Bunch{tools: List<&2, M.Tool>, moved: Bool}

# a directory the ancestry clone may use, under the ignored half of `.ez/`
def work() -> String:
  ".ez/pin-up"

# a tool left as it was
def stay(+t: M.Tool) -> Touched:
  Touched{t, False{}}

# a tool whose pin moved
def moved(+t: M.Tool) -> Touched:
  Touched{t, True{}}

# the pin with a commit and a NAR hash written in. An empty tag leaves the
# one the ledger already had. The vendor bit is off: a tool is not committed
# under `.ez/lib`.
def set.go(+n: String, +e: String, +b: String, s: M.Source, +rev: String,
  +tag: String, +nar: String) -> M.Tool:
  match s:
    case M.Hub{}:
      M.Tool{n, e, b, M.Hub{}}
    case M.Git{url, _rev, old, root, _nar, _vend}:
      M.Tool{n, e, b, M.Git{url, rev,
        Bool.pick(String, String.is_empty(tag), old, tag), M.root.or(root),
        nar, False{}}}

def set(+t: M.Tool, +rev: String, +tag: String, +nar: String) -> M.Tool:
  M.Tool{n, e, b, s} = t
  set.go(n, e, b, s, rev, tag, nar)

# either side moved
def either(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

# one tool in front of the rest
def join(a: Touched, b: Bunch) -> Bunch:
  Touched{t, m} = a
  Bunch{ts, any} = b
  Bunch{t <> ts, either(m, any)}

# a write that did not happen is a failure
def wrote(ok: Bool, +at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# the ledger, rewritten only when a pin moved
def write(mved: Bool, +name: String, +entry: String, +bin: String,
  ds: List<&2, M.Dep>, ts: List<&2, M.Tool>) -> IO(Unit):
  match mved:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        ok : Bool <- F.write("ez.toml", Rend.show(M.Manifest{name, entry, bin, ds, ts}))
        wrote(ok, "ez.toml")

# a tool with no repo cannot be pinned
def need.git(git: Bool, +name: String) -> IO(Unit):
  match git:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: tools." ++ name ++ " has no git")

# the ref to resolve: the tag the ledger named, or the default ref
def ref.of(no_tag: Bool, +url: String, +tag: String) -> IO(String):
  match no_tag:
    case False{}:
      IO.pure(String, tag)
    case True{}:
      Git.default.ref(url)

# a commit weighed, then written into the pin
def weighed(+t: M.Tool, +url: String, +rev: String, +tag: String) -> IO(Touched):
  do IO<Touched>:
    +nar : String <- Git.weigh(url, rev)
    return moved(set(t, rev, tag, nar))

# a rev that is already pinned, whose NAR hash is not
def fill.nar(+t: M.Tool) -> IO(Touched):
  +src = M.tool.source(t)
  weighed(t, M.source.url(src), M.source.rev(src), "")

# the commit a ref named, weighed
def fill.got(+t: M.Tool, +url: String, r: Git.Ref) -> IO(Touched):
  Git.Ref{+rev, tag} = r
  weighed(t, url, rev, tag)

# a pin with no commit: the tag, or the default ref, then the NAR hash
def fill.rev(+t: M.Tool) -> IO(Touched):
  +src = M.tool.source(t)
  +url = M.source.url(src)
  do IO<Touched>:
    +s : Say.Spin <- Say.hold(Say.resolving.at(M.tool.name(t)))
    +ref : String <- ref.of(String.is_empty(M.source.tag(src)), url,
      M.source.tag(src))
    r : Git.Ref <- Git.resolve(url, ref)
    Say.done(s)
    fill.got(t, url, r)

# a present rev whose NAR hash is or is not filled
def fill.nar.at(no_nar: Bool, +t: M.Tool) -> IO(Touched):
  match no_nar:
    case True{}:
      fill.nar(t)
    case False{}:
      IO.pure(Touched, stay(t))

# a missing rev is resolved; a missing NAR hash is filled; a full pin is kept
def fill.gap(no_rev: Bool, no_nar: Bool, +t: M.Tool) -> IO(Touched):
  match no_rev:
    case True{}:
      fill.rev(t)
    case False{}:
      fill.nar.at(no_nar, t)

# one tool, filled when its pin is short
def fill.one(+t: M.Tool) -> IO(Touched):
  +src = M.tool.source(t)
  do IO<Touched>:
    need.git(M.source.is_git(src), M.tool.name(t))
    fill.gap(String.is_empty(M.source.rev(src)),
      String.is_empty(M.source.nar(src)), t)

# every tool, in the order the ledger wrote them
def fill.walk(ts: List<&2, M.Tool>) -> IO(Bunch):
  match ts:
    case []:
      IO.pure(Bunch, Bunch{[], False{}})
    case +h <> t:
      do IO<Bunch>:
        +a : Touched <- fill.one(h)
        +b : Bunch <- fill.walk(t)
        return join(a, b)

# the branch a rev-only pin followed, said when there is one
def branch.of(+b: String) -> String:
  Bool.pick(String, String.is_empty(b), "", " (" ++ b ++ ")")

# a pin that moved
def say.move(+name: String, +old: String, +new: String, +branch: String) -> IO(Unit):
  IO.print(name ++ ": " ++ old ++ " -> " ++ new ++ branch.of(branch))

# a pin that was already where the remote points
def say.keep(+name: String, +rev: String) -> IO(Unit):
  IO.print(name ++ ": unchanged " ++ rev)

# the same commit, whose tree no longer hashes to the pin
def drift.why(+name: String, +rev: String) -> String:
  "ez: " ++ name ++ ": narHash drifted at " ++ rev

# a tag that moved off the pin's history, or a branch tip that does not
# descend from a rev-only pin
def off.why(+name: String, +tag: String, +pin: String, +tip: String) -> String:
  Bool.pick(String, String.is_empty(tag),
    "ez: " ++ name ++ ": " ++ pin ++ " is not an ancestor of " ++ tip,
    "ez: " ++ name ++ ": tag " ++ tag ++ " moved off " ++ pin)

# the word Off quotes: a branch name when we have one, otherwise the commit
def tip.of(+branch: String, +tip: String) -> String:
  Bool.pick(String, String.is_empty(branch), tip, branch)

# an empty recorded hash is not a disagreement; a different one is drift
def nar.kept(empty: Bool, same: Bool, +t: M.Tool, +rev: String, +nar: String) -> IO(Touched):
  match empty:
    case True{}:
      IO.pure(Touched, moved(set(t, rev, "", nar)))
    case False{}:
      match same:
        case True{}:
          do IO<Touched>:
            say.keep(M.tool.name(t), rev)
            return stay(t)
        case False{}:
          IO.die(Touched, 1, drift.why(M.tool.name(t), rev))

# the same commit, weighed
def up.keep(+t: M.Tool, +rev: String) -> IO(Touched):
  +src = M.tool.source(t)
  +old = M.source.nar(src)
  do IO<Touched>:
    +nar : String <- Git.weigh(M.source.url(src), rev)
    nar.kept(String.is_empty(old), String.eq(old, nar), t, rev, nar)

# a commit the pin moves to
def up.move(+t: M.Tool, +rev: String, +tag: String, +branch: String) -> IO(Touched):
  +src = M.tool.source(t)
  do IO<Touched>:
    +nar : String <- Git.weigh(M.source.url(src), rev)
    say.move(M.tool.name(t), M.source.rev(src), rev, branch)
    return moved(set(t, rev, tag, nar))

# the verdict, once the remote has been asked and the ancestry read
def judged(v: U.Verdict, +t: M.Tool, +pin: String, +tip: String,
  +branch: String) -> IO(Touched):
  match v:
    case U.Keep{}:
      up.keep(t, pin)
    case U.Drift{}:
      IO.die(Touched, 1, drift.why(M.tool.name(t), pin))
    case U.Off{}:
      IO.die(Touched, 1, off.why(M.tool.name(t), M.source.tag(M.tool.source(t)),
        pin, tip.of(branch, tip)))
    case U.Advance{+rev, tag}:
      up.move(t, rev, tag, branch)

# ancestry's answer turned into a verdict. The tree has not been weighed yet;
# a same commit is weighed in Keep.
def resolved(+t: M.Tool, +pin: String, +tip: String, +tag: String,
  +branch: String, onward: Bool) -> IO(Touched):
  judged(U.judge(String.eq(pin, tip), onward, True{}, tip, tag), t, pin, tip,
    branch)

# ancestry, then the verdict
def ask(+t: M.Tool, +pin: String, +tip: String, +tag: String,
  +branch: String) -> IO(Touched):
  do IO<Touched>:
    +on : Bool <- Git.descendant.at(work(), M.source.url(M.tool.source(t)), pin, tip)
    resolved(t, pin, tip, tag, branch, on)

# a recorded tag, re-resolved
def follow.got(+t: M.Tool, r: Git.Ref) -> IO(Touched):
  Git.Ref{+rev, tag} = r
  ask(t, M.source.rev(M.tool.source(t)), rev, tag, "")

def follow(+t: M.Tool, +ref: String) -> IO(Touched):
  do IO<Touched>:
    +s : Say.Spin <- Say.hold(Say.resolving.at(M.tool.name(t)))
    r : Git.Ref <- Git.resolve(M.source.url(M.tool.source(t)), ref)
    Say.done(s)
    follow.got(t, r)

# a rev-only pin, against the default branch tip
def forward.got(+t: M.Tool, tip: Git.Tip) -> IO(Touched):
  Git.Tip{+rev, +branch} = tip
  ask(t, M.source.rev(M.tool.source(t)), rev, "", branch)

def forward(+t: M.Tool) -> IO(Touched):
  do IO<Touched>:
    +s : Say.Spin <- Say.hold(Say.resolving.at(M.tool.name(t)))
    tip : Git.Tip <- Git.remote(M.source.url(M.tool.source(t)))
    Say.done(s)
    forward.got(t, tip)

# one selected tool
def up.one(a: U.Aim, +t: M.Tool) -> IO(Touched):
  match a:
    case U.Hold{}:
      IO.pure(Touched, stay(t))
    case U.Follow{ref}:
      follow(t, ref)
    case U.Forward{}:
      forward(t)

# a selected tool names a repo, or it cannot be re-pinned
def up.git(git: Bool, +t: M.Tool, +src: M.Source) -> IO(Touched):
  match git:
    case False{}:
      IO.die(Touched, 1, "ez: tools." ++ M.tool.name(t) ++ " has no git")
    case True{}:
      up.one(U.aim(True{}, src), t)

# a selected tool is asked; the others are left
def up.sel(sel: Bool, +t: M.Tool, +src: M.Source) -> IO(Touched):
  match sel:
    case False{}:
      IO.pure(Touched, stay(t))
    case True{}:
      up.git(M.source.is_git(src), t, src)

def up.ask(+t: M.Tool, +only: String) -> IO(Touched):
  +src = M.tool.source(t)
  up.sel(U.chosen(only, M.tool.name(t)), t, src)

# every tool
def up.walk(+only: String, ts: List<&2, M.Tool>) -> IO(Bunch):
  match ts:
    case []:
      IO.pure(Bunch, Bunch{[], False{}})
    case +h <> t:
      do IO<Bunch>:
        +a : Touched <- up.ask(h, only)
        +b : Bunch <- up.walk(only, t)
        return join(a, b)

# the walk, written when a pin moved
def bunch.put(+name: String, +entry: String, +bin: String, ds: List<&2, M.Dep>,
  b: Bunch) -> IO(Unit):
  match b:
    case Bunch{tools, mved}:
      write(mved, name, entry, bin, ds, tools)

# a ledger that parsed, with every short pin filled
def fill.good(m: M.Manifest) -> IO(Unit):
  M.Manifest{+name, +entry, +bin, +ds, +ts} = m
  do IO<Unit>:
    b : Bunch <- fill.walk(ts)
    bunch.put(name, entry, bin, ds, b)

# a ledger that parsed, with every selected pin re-asked
def up.good(m: M.Manifest, +only: String) -> IO(Unit):
  M.Manifest{+name, +entry, +bin, +ds, +ts} = m
  do IO<Unit>:
    b : Bunch <- up.walk(only, ts)
    bunch.put(name, entry, bin, ds, b)

# a ledger that parsed
def read.good(fill: Bool, m: M.Manifest, +only: String) -> IO(Unit):
  match fill:
    case True{}:
      fill.good(m)
    case False{}:
      up.good(m, only)

# the ledger on disk, or the reason it was not one
def read.go(r: M.Read, fill: Bool, +only: String) -> IO(Unit):
  match r:
    case M.Bad{why}:
      IO.die(Unit, 1, "ez: " ++ why)
    case M.Good{m}:
      read.good(fill, m, only)

# `ez lock`, filling a rev or a NAR hash a tool does not have yet
def fill() -> IO(Unit):
  do IO<Unit>:
    t : Maybe<&2, String> <- F.read("ez.toml")
    read.go(M.parse(F.text_of(t)), True{}, "")

# `ez lock --upgrade`, for every tool or for the one named
def upgrade(+only: String) -> IO(Unit):
  do IO<Unit>:
    t : Maybe<&2, String> <- F.read("ez.toml")
    read.go(M.parse(F.text_of(t)), False{}, only)
