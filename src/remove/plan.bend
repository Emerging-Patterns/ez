# remove/plan: `ez remove` as a pure planner. It asks nothing: its World is
# the name asked for, the ledger's text (None when there is no ez.toml) and
# `.gitignore`'s text ("" when there is none), and its planner is one function
# from that World to a Plan. The interpreter (remove/run.bend) reads the two
# files, calls it, and runs what it returns.
#
# The plan, when the ledger reads and names the dependency: ez.toml written
# with the dependency dropped (`Rend.remove`); `.gitignore` written with the
# allowlist `I.sync` derives from what is left, when that changes it; and
# the committed tree `.ez/lib/<hash>` of a dependency that was vendored
# removed, unless a dependency that is left still names that hash. Anything
# else is a refusal, with no effect at all: no ledger, one that does not
# parse, or a name the ledger does not have, which `cargo remove` refuses too.
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), which
# the add design moves to a shared plan/plan.bend later; see "Update (A1,
# A4)" in docs/rfc/ez-add-planner.md.
import Base
import ../lock/plan.bend as P
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../ledger/ignore.bend as I

# what `ez remove` reads: the name it was given, the ledger's text or None,
# and the ignore file's text, "" when there is none
type World is Data:
  World{name: String, ledger: Maybe<&2, String>, ignore: String}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the ignore file's path, which is fixed
def ignore.file() -> String:
  ".gitignore"

# the ledger as read: what the file says, or, with no file, a read that did
# not parse and says why. A missing ledger is not an empty one to write back.
def read.of(got: Maybe<&2, String>) -> M.Read:
  match got:
    case None{}:
      M.Bad{"no " ++ toml() ++ " here; ez remove works on a project's " ++
        "ledger, and ez init makes one"}
    case Some{text}:
      M.parse(text)

# the dependencies of a ledger that was read
def deps.of(manifest: M.Manifest) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, _pa, _pv, ds, _ts} = manifest
  ds

# the rest of a scan only when this one was not it
def any.step(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a dependency has this name
def named(ds: List<&2, M.Dep>, +name: String) -> Bool:
  match ds:
    case []:
      False{}
    case +h <> t:
      any.step(String.eq(M.dep.name(h), name), _u => named(t, name))

# whether a dependency names this hash
def holds(ds: List<&2, M.Dep>, +hash: String) -> Bool:
  match ds:
    case []:
      False{}
    case +h <> t:
      any.step(String.eq(M.dep.hash(h), hash), _u => holds(t, hash))

# whether a char may stand in a hash that names a directory under `.ez/lib`
def char.ok(+ch: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(ch, '/'), Char.is_eq(ch, '\\')))

# whether every char of a text may
def chars.ok(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      +rest = chars.ok(t)
      Bool.and(char.ok(h), rest)

# a hash `rm -rf .ez/lib/<hash>` removes one tree for: a `0x` name with no
# path separator in it. `M.parse` does not check a hash's shape, and a ledger
# is text a person edits, so this is checked before a tree is removed.
def safe(+hash: String) -> Bool:
  Bool.and(String.starts_with(hash, "0x"), chars.ok(hash))

# a vendored hash, removed ahead of the rest when it is safe to remove and no
# dependency that is left names it
def gone.hash(keep: Bool, +hash: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      rest
    case False{}:
      hash <> rest

# a dependency's committed tree, when it is the one removed and is vendored
def gone.put(hit: Bool, +hash: String, +left: List<&2, M.Dep>, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      gone.hash(Bool.or(holds(left, hash), Bool.not(safe(hash))), hash, rest)
    case False{}:
      rest

# the committed trees removing `name` leaves no dependency to name: the hash
# of each vendored dependency by that name that none in `left` names
def gone(ds: List<&2, M.Dep>, +name: String, +left: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      gone.put(Bool.and(String.eq(M.dep.name(h), name),
        M.source.vendor(M.source.dep(h))), M.dep.hash(h), left, gone(t, name, left))

# `.gitignore` written ahead of the rest when the allowlist changes it
def ignore.put(same: Bool, +next: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match same:
    case True{}:
      rest
    case False{}:
      P.Write{ignore.file(), next} <> rest

# what `ez remove` does to a ledger that names the dependency: the ledger
# written without it, the allowlist derived from what is left, and each
# committed tree it leaves unnamed removed
def edits(+led: M.Manifest, +name: String, +ignore: String) -> List<&2, P.Effect>:
  +left = deps.of(Rend.remove(led, name))
  +next = I.sync(left, ignore)
  P.Write{toml(), Rend.show(Rend.remove(led, name))} <>
    ignore.put(String.eq(next, ignore), next,
      P.drops.of(gone(deps.of(led), name, left), []))

# the refusal for a name the ledger does not have
def absent(+name: String) -> String:
  "ez: " ++ toml() ++ " has no dependency named " ++ name

# the refusal for a ledger that names the dependency but, with it dropped,
# cannot be written so that it reads back (EZ-LED-4), or for a name it does
# not have
def refusal(named: Bool, +name: String) -> String:
  Bool.pick(String, named, Rend.unrenderable(), absent(name))

# the plan for a ledger that read: the edits when it names the dependency and
# the ledger left can be written, a refusal when not
def plan.has(has: Bool, +led: M.Manifest, +name: String, +ignore: String) -> P.Plan:
  match has:
    case True{}:
      P.Plan{edits(led, name, ignore), P.Success{}}
    case False{}:
      P.Plan{[], P.Refused{refusal(named(deps.of(led), name), name)}}

# the plan for the ledger as read. One that did not read, or is not there,
# is refused before anything else, and its reason is the one every command
# that edits a ledger gives.
def plan.read(led: M.Read, +name: String, +ignore: String) -> P.Plan:
  match led:
    case M.Bad{why}:
      P.Plan{[], P.Refused{"ez: " ++ M.show(M.Bad{why})}}
    case M.Good{+m}:
      plan.has(Bool.and(named(deps.of(m), name), Rend.renderable(Rend.remove(m, name))),
        m, name, ignore)

# `ez remove` over a World
def plan(world: World) -> P.Plan:
  World{+n, l, +ig} = world
  plan.read(read.of(l), n, ig)

# whether a plan ends in a refusal
def refuses.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether `ez remove` refuses on a World
def refuses(world: World) -> Bool:
  refuses.plan(plan(world))

# what a path holds once a plan has run, when it held `was` before
def after(wrote: P.Wrote, +was: String) -> String:
  match wrote:
    case P.Kept{}:
      was
    case P.Put{text}:
      text
