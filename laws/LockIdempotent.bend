# `ez lock` is idempotent: run on the world it just produced, it writes the
# same bytes.
#
# This guarantee is proved for a plain lock and for `ez lock --upgrade`.
# `after` (laws/defs/WorldAfterLock.bend) is the World a lock leaves for the
# next to read: a refused lock leaves the World it read; one that succeeded
# leaves every tree it laid read from BEND_LIB with the bytes laid, and an
# upgrade also leaves the ledger it wrote, the committed sources as it
# rewrote them, and `.gitignore` as it left it. The remote does not change
# between the two runs: every question the second upgrade asks a remote is
# answered as the first run's answers say. Run again on that World, `ez lock
# --upgrade` writes the same bytes to ez.lock.toml (`upgrade_idempotent`),
# renders the same ledger model (`reupgrade_moves_nothing`), so writes no
# ez.toml (`upgrade_settles`), lays nothing new (`reupgrade_lays_nothing`),
# and writes no path but the lock (`reupgrade_writes_only_lock`), the last
# for a ledger whose vendored hashes hold no newline, as
# laws/GitignoreAllowlistIsLedger.bend's text layer requires. Each rests on
# the ez.toml the first run wrote reading back as the model it rendered,
# which is laws/WrittenLedgerReadsBack.bend, and each takes that as its
# premise `ReadsBack` (eztoml's round trip, trusted in src/toml/toml.bend).
# The key step is that a pin at its own tip is kept: the second run asks
# each selected pin the question the first asked, gets the tip it moved to,
# and checks the tree out again, which agrees with the hash, narHash and
# root the first run wrote. That a vendored tree laid under `.ez/lib` is
# read from BEND_LIB holds when BEND_LIB is `.ez/lib`, its default; with
# BEND_LIB elsewhere it is cloned again, and `clone_reproduces` says the
# lock is the same.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/ignore.bend as I
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ./defs/LedgerReadsBackPremise.bend as D1
import ./defs/LockInputs.bend as D2
import ./defs/WorldAfterLock.bend as D3

# the hash of an answer a clone gave that passed every check: a tree the next
# plan would lay
def fresh.how(
  how: W.How,
  +orgs: List<&2, L.Origin>,
  +hub: String,
  +hash: String,
  +manifest: String,
  +ss: List<&2, String>
) -> List<&2, String>:
  match how:
    case W.Lib{}:
      []
    case W.Clone{+got}:
      Bool.pick(List<&2, String>,
        D2.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})), [hash], [])
    case W.Served{}:
      []

def fresh.one(+orgs: List<&2, L.Origin>, +hub: String, +hash: String, answer: W.Answer) -> List<&2, String>:
  match answer:
    case W.Miss{_why}:
      []
    case W.Got{how, manifest, ss}:
      fresh.how(how, orgs, hub, hash, manifest, ss)
    case W.Said{_text}:
      []
    case W.Locked{_text}:
      []

def fresh.all(+orgs: List<&2, L.Origin>, +hub: String, rs: List<&2, W.Reply>) -> List<&2, String>:
  match rs:
    case []:
      []
    case W.Reply{ask, answer} <> t:
      +hash = W.ask.hash(ask)
      List.append(&2, String, fresh.one(orgs, hub, hash, answer), fresh.all(orgs, hub, t))

# every tree a World's clones answered that passed every check. In a World
# that asks about each hash once, which is every World the interpreter
# gathers, these are the trees a plain lock that succeeds lays (`P.lays` over
# `P.cloned`). Law vocabulary: ez never calls it.
def fresh.origins(world: W.World) -> List<&2, String>:
  W.World{+args, +ledger, _listing, replies, +ups} = world
  fresh.all(W.next.origins(W.next(args, ledger, ups)),
    W.next.hub(W.next(args, ledger, ups)), replies)

# LAW: plain `ez lock` is idempotent. Run again on the World it leaves, it
# writes the same bytes to ez.lock.toml, or, when it refused, refuses again
# and writes none. A laid tree read from BEND_LIB is judged as the clone that
# passed was, which is `clone_reproduces` read backwards.
law lock_idempotent:
  for +w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.put(D3.after(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: and it lays nothing new. On the World a lock that succeeded leaves, no
# tree arrives by a clone that passes, so every tree the next lock reads that
# passes was read from BEND_LIB or served by the hub, and none is laid again.
law relock_lays_nothing:
  for +w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  {fresh.origins(D3.after(w)) == [] : List<&2, String>}

# `ez lock --upgrade` is idempotent too. Run again on the World it leaves,
# against a remote that did not change, every pin is at its own tip: the
# second run asks each selected pin's remote the question the first asked,
# gets the tip it moved to, finds the pin at it, and checks the tree out
# again, which agrees with the hash, narHash and root the first run wrote, so
# it keeps the pin. Nothing moves, so it writes no ez.toml, no source and no
# tree, and the lock it writes is the one the first run wrote.
#
# The second run reads ez.toml's bytes, and the ledger the first run wrote
# reads back as the model it rendered, `P.ledger.next`
# (`upgrade_reads_back`, laws/WrittenLedgerReadsBack.bend). An upgrade that
# moved nothing wrote no ledger, and reads back as it is. The upgrade laws
# of laws/UpgradeHoldsHub.bend, laws/UpgradeRevMovesForward.bend,
# laws/UpgradeOnlyNamedPackage.bend and laws/UpgradeTagFollows.bend are
# stated over the same model.

# LAW: `ez lock --upgrade`, run again on the World it leaves, writes the same
# bytes to ez.lock.toml, or, when it refused, refuses again and writes none
law upgrade_idempotent:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for rb: D1.ReadsBack()
  {P.put(D3.after(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: and it moves nothing: the ledger model it renders is the one the first
# run rendered
law reupgrade_moves_nothing:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for rb: D1.ReadsBack()
  {P.ledger.next(D3.after(w)) == P.ledger.next(w) : M.Read}

# LAW: so, after one that succeeded, it does not write ez.toml
law upgrade_settles:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for rb: D1.ReadsBack()
  {P.put(D3.after(w), "ez.toml") == P.Kept{} : P.Wrote}

# LAW: and it lays nothing new: every tree the first run laid is read from
# BEND_LIB, and no tree arrives by a clone that passes
law reupgrade_lays_nothing:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for rb: D1.ReadsBack()
  {fresh.origins(D3.after(w)) == [] : List<&2, String>}

# LAW: and it writes no path but the lock: no ez.toml, no source and no
# `.gitignore`, since the `.gitignore` the first run left is already in sync
# with the ledger it left (`sync_idempotent`), for a ledger whose vendored
# hashes hold no newline, as a `0x` name never does
law reupgrade_writes_only_lock:
  for +w: W.World
  for +p: String
  for u: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for ev: {Str.clear.all(I.vended(D2.ledger.deps(P.ledger.next(w))), '\n') == True{} : Bool}
  for ne: {String.eq("ez.lock.toml", p) == False{} : Bool}
  for rb: D1.ReadsBack()
  {P.put(D3.after(w), p) == P.Kept{} : P.Wrote}
