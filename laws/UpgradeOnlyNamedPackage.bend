# `--package NAME` asks the remote to resolve only the named dependency or
# tool, and every other ledger entry keeps its rev, tag and hash. Resolving is
# asking for refs, the default branch, ancestry, or a checkout at a new rev.
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ./defs/LockInputs.bend as D1

# What `ez lock --upgrade` keeps and what it asks about. These laws are
# stated over `P.ledger.next`, the ledger model the upgrade renders into
# ez.toml, which is what the file's bytes read back as
# (`upgrade_reads_back`, laws/WrittenLedgerReadsBack.bend), so they hold of
# the bytes. Whatever the remote answered, and on every round of questions,
# the model keeps the entries these name. `W.dep(w, n)` is the dependency
# ez.toml records under `n`, as `M.dep` finds it, the first of that name.

# the tool a ledger pins under a name, as `M.tool.find` finds it. Law
# vocabulary: ez never calls it.
def tool.at(ledger: M.Read, name: String) -> M.Tool:
  M.tool.find(M.tools_of(ledger), name)

# the upgrade's answers a World holds
def ups.of(world: W.World) -> List<&2, Up.Reply>:
  W.World{_args, _ledger, _listing, _replies, ups} = world
  ups

# LAW: `--package n` leaves every dependency of another name as ez.toml has
# it: its rev, tag, hash, and every other field
law upgrade_one_frames_deps:
  for +w: W.World
  for +n: String
  for +m: String
  for e: {W.args.only(w) == n : String}
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {M.dep(P.ledger.next(w), m) == W.dep(w, m) : M.Dep}

# LAW: and every tool of another name
law upgrade_one_frames_tools:
  for +w: W.World
  for +n: String
  for +m: String
  for e: {W.args.only(w) == n : String}
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {tool.at(P.ledger.next(w), m) == tool.at(W.parsed(W.ledger.of(w)), m) : M.Tool}

# LAW: and `ez lock --upgrade --package n` asks the remote exactly what it
# asks of a ledger holding nothing but the entries named `n`, on every round
# of questions. Refs, the default branch, tags, ancestry and checkouts are
# asked of those entries alone; no other dependency or tool reaches the
# remote, or changes a question that is asked.
law upgrade_one_asks_alone:
  for +w: W.World
  for +n: String
  for u: {W.args.upgrade(w) == True{} : Bool}
  for e: {W.args.only(w) == n : String}
  for ne: {String.is_empty(n) == False{} : Bool}
  {P.wants.up(w) == Up.next.asks(Up.next(n, D1.alone(W.parsed(W.ledger.of(w)), n), ups.of(w)))
    : List<&2, Up.Ask>}
