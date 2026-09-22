# ez/pin: `ez lock --upgrade` fills a `[tools.*]` pin or moves one, and a
# plain `ez lock` refuses a pin it would have to fill. A tag is re-resolved to
# a commit and the NAR hash is filled, the way a git dependency is pinned. The
# checkout is weighed and removed. Nothing is laid under `.ez/lib`, and no
# import line is rewritten: a tool is not a package.
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
def stay(+tool: M.Tool) -> Touched:
  Touched{tool, False{}}

# a tool whose pin moved
def moved(+tool: M.Tool) -> Touched:
  Touched{tool, True{}}

# the pin with a commit and a NAR hash written in. An empty tag leaves the
# one the ledger already had. The vendor bit is off: a tool is not committed
# under `.ez/lib`.
def set.go(
  +name: String,
  +entry: String,
  +bin: String,
  source: M.Source,
  +rev: String,
  +tag: String,
  +nar: String
) -> M.Tool:
  match source:
    case M.Hub{}:
      M.Tool{name, entry, bin, M.Hub{}}
    case M.Git{url, _rev, old, root, _nar, _vend}:
      M.Tool{name, entry, bin, M.Git{url, rev,
        Bool.pick(String, String.is_empty(tag), old, tag), M.root.or(root),
        nar, False{}}}

# a tool's pin with a commit, a tag and a NAR hash written in
def set(+tool: M.Tool, +rev: String, +tag: String, +nar: String) -> M.Tool:
  M.Tool{n, e, b, s} = tool
  set.go(n, e, b, s, rev, tag, nar)

# either side moved
def either(left: Bool, right: Bool) -> Bool:
  match left:
    case True{}:
      True{}
    case False{}:
      right

# one tool in front of the rest
def join(one: Touched, rest: Bunch) -> Bunch:
  Touched{t, m} = one
  Bunch{ts, any} = rest
  Bunch{t <> ts, either(m, any)}

# a write that did not happen is a failure
def wrote(ok: Bool, +at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# the ledger, rewritten only when a pin moved
def write(
  mved: Bool,
  +name: String,
  +entry: String,
  +bin: String,
  +hub: String,
  ds: List<&2, M.Dep>,
  ts: List<&2, M.Tool>
) -> IO(Unit):
  match mved:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        ok : Bool <- F.write("ez.toml", Rend.show(M.Manifest{name, entry, bin, hub, ds, ts}))
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
def weighed(+tool: M.Tool, +url: String, +rev: String, +tag: String) -> IO(Touched):
  do IO<Touched>:
    +nar : String <- Git.weigh(url, rev)
    return moved(set(tool, rev, tag, nar))

# a rev that is already pinned, whose NAR hash is not
def fill.nar(+tool: M.Tool) -> IO(Touched):
  +src = M.tool.source(tool)
  weighed(tool, M.source.url(src), M.source.rev(src), "")

# the commit a ref named, weighed
def fill.got(+tool: M.Tool, +url: String, answer: Git.Ref) -> IO(Touched):
  Git.Ref{+rev, tag} = answer
  weighed(tool, url, rev, tag)

# a pin with no commit: the tag, or the default ref, then the NAR hash
def fill.rev(+tool: M.Tool) -> IO(Touched):
  +src = M.tool.source(tool)
  +url = M.source.url(src)
  do IO<Touched>:
    +s : Say.Spin <- Say.hold(Say.resolving.at(M.tool.name(tool)))
    +ref : String <- ref.of(String.is_empty(M.source.tag(src)), url,
      M.source.tag(src))
    r : Git.Ref <- Git.resolve(url, ref)
    Say.done(s)
    fill.got(tool, url, r)

# a present rev whose NAR hash is or is not filled
def fill.nar.at(no_nar: Bool, +tool: M.Tool) -> IO(Touched):
  match no_nar:
    case True{}:
      fill.nar(tool)
    case False{}:
      IO.pure(Touched, stay(tool))

# a missing rev is resolved; a missing NAR hash is filled; a full pin is kept
def fill.gap(no_rev: Bool, no_nar: Bool, +tool: M.Tool) -> IO(Touched):
  match no_rev:
    case True{}:
      fill.rev(tool)
    case False{}:
      fill.nar.at(no_nar, tool)

# one tool, filled when its pin is short
def fill.one(+tool: M.Tool) -> IO(Touched):
  +src = M.tool.source(tool)
  do IO<Touched>:
    need.git(M.source.is_git(src), M.tool.name(tool))
    fill.gap(String.is_empty(M.source.rev(src)),
      String.is_empty(M.source.nar(src)), tool)

# the branch a rev-only pin followed, said when there is one
def branch.of(+label: String) -> String:
  Bool.pick(String, String.is_empty(label), "", " (" ++ label ++ ")")

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
def nar.kept(empty: Bool, same: Bool, +tool: M.Tool, +rev: String, +nar: String) -> IO(Touched):
  match empty:
    case True{}:
      IO.pure(Touched, moved(set(tool, rev, "", nar)))
    case False{}:
      match same:
        case True{}:
          do IO<Touched>:
            say.keep(M.tool.name(tool), rev)
            return stay(tool)
        case False{}:
          IO.die(Touched, 1, drift.why(M.tool.name(tool), rev))

# the same commit, weighed
def up.keep(+tool: M.Tool, +rev: String) -> IO(Touched):
  +src = M.tool.source(tool)
  +old = M.source.nar(src)
  do IO<Touched>:
    +nar : String <- Git.weigh(M.source.url(src), rev)
    nar.kept(String.is_empty(old), String.eq(old, nar), tool, rev, nar)

# a commit the pin moves to
def up.move(+tool: M.Tool, +rev: String, +tag: String, +branch: String) -> IO(Touched):
  +src = M.tool.source(tool)
  do IO<Touched>:
    +nar : String <- Git.weigh(M.source.url(src), rev)
    say.move(M.tool.name(tool), M.source.rev(src), rev, branch)
    return moved(set(tool, rev, tag, nar))

# the verdict, once the remote has been asked and the ancestry read
def judged(verdict: U.Verdict, +tool: M.Tool, +pin: String, +tip: String, +branch: String) -> IO(Touched):
  match verdict:
    case U.Keep{}:
      up.keep(tool, pin)
    case U.Drift{}:
      IO.die(Touched, 1, drift.why(M.tool.name(tool), pin))
    case U.Off{}:
      IO.die(Touched, 1, off.why(M.tool.name(tool), M.source.tag(M.tool.source(tool)),
        pin, tip.of(branch, tip)))
    case U.Advance{+rev, tag}:
      up.move(tool, rev, tag, branch)

# ancestry's answer turned into a verdict. The tree has not been weighed yet;
# a same commit is weighed in Keep.
def resolved(+tool: M.Tool, +pin: String, +tip: String, +tag: String, +branch: String, onward: Bool) -> IO(Touched):
  judged(U.judge(String.eq(pin, tip), onward, True{}, tip, tag), tool, pin, tip,
    branch)

# ancestry, then the verdict
def ask(+tool: M.Tool, +pin: String, +tip: String, +tag: String, +branch: String) -> IO(Touched):
  do IO<Touched>:
    +on : Bool <- Git.descendant.at(work(), M.source.url(M.tool.source(tool)), pin, tip)
    resolved(tool, pin, tip, tag, branch, on)

# a recorded tag, re-resolved
def follow.got(+tool: M.Tool, answer: Git.Ref) -> IO(Touched):
  Git.Ref{+rev, tag} = answer
  ask(tool, M.source.rev(M.tool.source(tool)), rev, tag, "")

# a tag pin, re-resolved at the remote
def follow(+tool: M.Tool, +ref: String) -> IO(Touched):
  do IO<Touched>:
    +s : Say.Spin <- Say.hold(Say.resolving.at(M.tool.name(tool)))
    r : Git.Ref <- Git.resolve(M.source.url(M.tool.source(tool)), ref)
    Say.done(s)
    follow.got(tool, r)

# a rev-only pin, against the default branch tip
def forward.got(+tool: M.Tool, tip: Git.Tip) -> IO(Touched):
  Git.Tip{+rev, +branch} = tip
  ask(tool, M.source.rev(M.tool.source(tool)), rev, "", branch)

# a rev-only pin, against the remote's default branch
def forward(+tool: M.Tool) -> IO(Touched):
  do IO<Touched>:
    +s : Say.Spin <- Say.hold(Say.resolving.at(M.tool.name(tool)))
    tip : Git.Tip <- Git.remote(M.source.url(M.tool.source(tool)))
    Say.done(s)
    forward.got(tool, tip)

# one selected tool
def up.one(aim: U.Aim, +tool: M.Tool) -> IO(Touched):
  match aim:
    case U.Hold{}:
      IO.pure(Touched, stay(tool))
    case U.Follow{ref}:
      follow(tool, ref)
    case U.Forward{}:
      forward(tool)

# a selected pin with no commit or no NAR hash is filled, which is the only
# place one is; a full one is asked whether it moved
def up.fill(short: Bool, +tool: M.Tool, +src: M.Source) -> IO(Touched):
  match short:
    case True{}:
      fill.one(tool)
    case False{}:
      up.one(U.aim(True{}, src), tool)

# a selected tool names a repo, or it cannot be re-pinned
def up.git(git: Bool, +tool: M.Tool, +src: M.Source) -> IO(Touched):
  match git:
    case False{}:
      IO.die(Touched, 1, "ez: tools." ++ M.tool.name(tool) ++ " has no git")
    case True{}:
      up.fill(Bool.or(String.is_empty(M.source.rev(src)),
        String.is_empty(M.source.nar(src))), tool, src)

# a selected tool is asked; the others are left
def up.sel(sel: Bool, +tool: M.Tool, +src: M.Source) -> IO(Touched):
  match sel:
    case False{}:
      IO.pure(Touched, stay(tool))
    case True{}:
      up.git(M.source.is_git(src), tool, src)

def up.ask(+tool: M.Tool, +only: String) -> IO(Touched):
  +src = M.tool.source(tool)
  up.sel(U.chosen(only, M.tool.name(tool)), tool, src)

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
def bunch.put(+name: String, +entry: String, +bin: String, +hub: String, ds: List<&2, M.Dep>, tally: Bunch) -> IO(Unit):
  match tally:
    case Bunch{tools, mved}:
      write(mved, name, entry, bin, hub, ds, tools)

# a ledger that parsed, with every selected pin filled or re-asked
def up.good(manifest: M.Manifest, +only: String) -> IO(Unit):
  M.Manifest{+name, +entry, +bin, +hub, +ds, +ts} = manifest
  do IO<Unit>:
    b : Bunch <- up.walk(only, ts)
    bunch.put(name, entry, bin, hub, ds, b)

# the ledger on disk, or the reason it was not one
def read.go(ledger: M.Read, +only: String) -> IO(Unit):
  match ledger:
    case M.Bad{why}:
      IO.die(Unit, 1, "ez: " ++ why)
    case M.Good{m}:
      up.good(m, only)

# `ez lock --upgrade`, for every tool or for the one named. A pin with no
# commit or no NAR hash is filled here and nowhere else.
def upgrade(+only: String) -> IO(Unit):
  do IO<Unit>:
    t : Maybe<&2, String> <- F.read("ez.toml")
    read.go(M.parse(F.text_of(t)), only)

# why a plain lock cannot copy a git pin as it stands, or "" when it can. The
# lock copies `rev` and `narHash` out of the ledger and never asks a remote
# for them, so a pin missing either is refused rather than filled, and the
# upgrade that fills it is named.
def gap.git(no_rev: Bool, no_nar: Bool, +name: String) -> String:
  match no_rev:
    case True{}:
      "ez: tools." ++ name ++ " has no rev; run `ez lock --upgrade --package " ++
        name ++ "` to pin it"
    case False{}:
      match no_nar:
        case True{}:
          "ez: tools." ++ name ++ " has no narHash; run `ez lock --upgrade --package " ++
            name ++ "` to pin it"
        case False{}:
          ""

# why a plain lock cannot copy a pin as it stands, or "" when it can. A pin
# with no repo has nothing to pin, under a plain lock or an upgrade.
def gap(pin: M.Tool) -> String:
  M.Tool{n, _e, _b, s} = pin
  match s:
    case M.Hub{}:
      "ez: tools." ++ n ++ " has no git"
    case M.Git{_url, rev, _tag, _root, nar, _vend}:
      gap.git(String.is_empty(rev), String.is_empty(nar), n)

# this pin's gap when it has one, otherwise the rest's. The rest arrives as a
# thunk and only the arm that wants it applies it, so the first gap stops the
# scan.
def gaps.step(none: Bool, here: String, rest: Unit -> String) -> String:
  match none:
    case True{}:
      rest(Unit{})
    case False{}:
      here

# the first pin, in ledger order, a plain lock cannot copy, or "" when it can
# copy every one
def gaps(ts: List<&2, M.Tool>) -> String:
  match ts:
    case []:
      ""
    case h <> t:
      +here = gap(h)
      gaps.step(String.is_empty(here), here, _u => gaps(t))

# a gap stops the lock before anything is written
def need.judge(+why: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(why), IO.pure(Unit, Unit{}),
    IO.die(Unit, 1, why))

# the ledger's pins, each complete, or the reason one is not
def need.go(ledger: M.Read) -> IO(Unit):
  match ledger:
    case M.Bad{why}:
      IO.die(Unit, 1, "ez: " ++ why)
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _ds, ts} = m
      need.judge(gaps(ts))

# `ez lock`: every `[tools.*]` pin already has a commit and a NAR hash, or the
# lock refuses. Nothing is resolved and ez.toml is not written.
def need() -> IO(Unit):
  do IO<Unit>:
    t : Maybe<&2, String> <- F.read("ez.toml")
    need.go(M.parse(F.text_of(t)))
