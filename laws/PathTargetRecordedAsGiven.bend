# A path target is recorded in the ledger as it was given, with a leading `~/`
# expanded, and a relative path resolves against the project root wherever git
# reads it: `ez add`, `ez lock`, `ez fetch` and `ez lock --upgrade`.
#
# This guarantee is proved for every command that reads a source. `P.anchor`
# keeps a URL and an absolute path and joins a relative path to the project
# root. `ez add` records the target as given, a path with only `~` expanded
# against HOME (`add_records_as_given`, `add_path_as_given`). `ez fetch`
# writes no file (`fetch_keeps_records`). `ez lock`, plain or `--upgrade`,
# records in the lock the source the ledger it is made from records for each
# package (`lock_records_as_given`), and `ez lock --upgrade` renders a model
# whose dependencies and tool pins record ez.toml's sources in ez.toml's
# order (`upgrade_records_as_given`, `upgrade_records_tools_as_given`),
# which is what ez.toml's bytes read back as
# (laws/WrittenLedgerReadsBack.bend). Every question git is asked names the
# source anchored at the project, as the planner computes it: `ez add`'s
# (`add_asks_anchored`), `ez fetch`'s checkouts (`fetch_asks_anchored`), `ez
# lock`'s package questions (`lock_asks_anchored`), and the upgrade's, each
# put to git as `Up.anchor` of the question the upgrade looks its answer up
# by, which are exactly `P.wants.up` (`upgrade_asks_anchored`,
# `upgrade_asks_its_questions`). That the interpreter hands git the source a
# question names is trusted in src/ez/app.bend.
import Base
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/ez/target.bend as Tgt
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ./defs/LockInputs.bend as D1

# the package questions a step asks, none when it runs its plan
def step.pkgs(st: P.Step) -> List<&2, W.Ask>:
  match st:
    case P.Asking{asks, _ups, _names}:
      asks
    case P.Run{_plan}:
      []

# the upgrade's queries a step asks, none when it runs its plan
def step.queries(st: P.Step) -> List<&2, P.Query>:
  match st:
    case P.Asking{_asks, ups, _names}:
      ups
    case P.Run{_plan}:
      []

# whether a package question names the source `orgs` records for its hash,
# anchored at `here`
def pkg.anchored(+here: String, +orgs: List<&2, L.Origin>, ask: W.Ask) -> Bool:
  match ask:
    case W.Pkg{+h, src, _hub}:
      String.eq(L.src.url(src), L.src.url(P.anchor.src(here, L.origin(orgs, h))))
    case _:
      True{}

# whether every package question does
def pkgs.anchored(+here: String, +orgs: List<&2, L.Origin>, as: List<&2, W.Ask>) -> Bool:
  match as:
    case []:
      True{}
    case h <> t:
      +rest = pkgs.anchored(here, orgs, t)
      Bool.and(pkg.anchored(here, orgs, h), rest)

# whether git is asked a query as the upgrade's question with its source
# anchored at `here`
def query.anchored(+here: String, query: P.Query) -> Bool:
  P.Query{ask, git} = query
  String.eq(Up.key(git), Up.key(Up.anchor(here, ask)))

# whether every query is
def queries.anchored(+here: String, qs: List<&2, P.Query>) -> Bool:
  match qs:
    case []:
      True{}
    case h <> t:
      +rest = queries.anchored(here, t)
      Bool.and(query.anchored(here, h), rest)

# the upgrade's questions a list of queries asks
def queries.asks(qs: List<&2, P.Query>) -> List<&2, Up.Ask>:
  match qs:
    case []:
      []
    case P.Query{ask, _git} <> t:
      ask <> queries.asks(t)

# LAW: every package question `ez lock` asks, plain or `--upgrade`, names the
# source the ledger it is made from records for that package, anchored at
# the project: a URL and an absolute path as they are, and a relative path
# joined to the project root
law lock_asks_anchored:
  for +w: W.World
  {pkgs.anchored(W.args.here(w), D1.origins(w), step.pkgs(P.step(w))) == True{} : Bool}

# LAW: the upgrade's questions a step puts to git are exactly the questions
# the upgrade still has (`P.wants.up`), the ones laws/UpgradeHoldsHub.bend,
# laws/UpgradeRevMovesForward.bend, laws/UpgradeOnlyNamedPackage.bend and
# laws/UpgradeTagFollows.bend are stated over
law upgrade_asks_its_questions:
  for +w: W.World
  {queries.asks(step.queries(P.step(w))) == P.wants.up(w) : List<&2, Up.Ask>}

# LAW: and git is asked each with the source it names anchored at the
# project, while the upgrade looks the answer up by the source as the ledger
# records it
law upgrade_asks_anchored:
  for +w: W.World
  {queries.anchored(W.args.here(w), step.queries(P.step(w))) == True{} : Bool}

# LAW: every package `ez lock` resolves, plain or `--upgrade`, and so every
# package its lock renders, carries the source the ledger it is made from
# records for its hash, as that ledger gives it, never anchored
law lock_records_as_given:
  for +w: W.World
  {D1.pinned.all(D1.origins(w), P.packs(w)) == P.packs(w) : List<&2, L.Pack>}

# the source a dependency records
def dep.url(dep: M.Dep) -> String:
  M.source.url(M.source.dep(dep))

# the sources dependencies record, in order
def dep.urls(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case h <> t:
      dep.url(h) <> dep.urls(t)

# the source a tool pin records
def tool.url(pin: M.Tool) -> String:
  M.source.url(M.tool.source(pin))

# the sources tool pins record, in order
def tool.urls(ts: List<&2, M.Tool>) -> List<&2, String>:
  match ts:
    case []:
      []
    case h <> t:
      tool.url(h) <> tool.urls(t)

# the tool pins of a ledger model, none when it did not parse
def ledger.tools(read: M.Read) -> List<&2, M.Tool>:
  match read:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _hpa, _hpv, _ds, ts} = m
      ts

# LAW: the ledger model `ez lock --upgrade` renders into ez.toml records every
# dependency's source as ez.toml gave it: the same sources, in the same
# order, a relative path still relative to the project. A pin that moves is
# retargeted to a new commit of the same source. A plain lock renders
# ez.toml's model as it is.
law upgrade_records_as_given:
  for +w: W.World
  {dep.urls(D1.ledger.deps(P.ledger.next(w))) == dep.urls(D1.ledger.deps(W.parsed(W.ledger.of(w))))
    : List<&2, String>}

# LAW: and every tool pin's source the same way
law upgrade_records_tools_as_given:
  for +w: W.World
  {tool.urls(ledger.tools(P.ledger.next(w))) == tool.urls(ledger.tools(W.parsed(W.ledger.of(w))))
    : List<&2, String>}

# LAW: the source recorded is the target as it was given: a URL as it is, a
# path with a leading `~/` expanded (`add_path_as_given`)
law add_records_as_given:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.url(M.source.dep(AP.added(w))) == A.url(w) : String}

# LAW: a path target is that path, with only `~` expanded against HOME: a
# relative one stays relative to the project
law add_path_as_given:
  for +w: A.World
  for +p: String
  for e: {Tgt.classify(A.target(w)) == Tgt.Local{p} : Tgt.Place}
  {A.url(w) == Tgt.expand(A.home(w), p) : String}

# LAW: every question `ez add` asks git names the source anchored where ez
# runs, which is the project root, so a relative path resolves against it
law add_asks_anchored:
  for +w: A.World
  {AP.asks.from(AP.wants(w), Path.anchor(A.here(w), A.url(w))) == True{} : Bool}

# LAW: every checkout `ez fetch` asks for is asked of the source the lock
# records for that package, anchored at the project: a URL and an absolute
# path as they are, and a relative path joined to the directory the project
# is in, wherever ez was run from
law fetch_asks_anchored:
  for +w: F.World
  {FP.asks.anchored(F.here(w), F.sects(w), FP.wants(w)) == True{} : Bool}

# LAW: and `ez fetch` writes no file, so the lock and ez.toml keep every
# source as it was recorded; it only lays trees
law fetch_keeps_records:
  for +w: F.World
  for +path: String
  {P.put.plan(FP.plan(w), path) == P.Kept{} : P.Wrote}

# LAW: a URL is fetched as it is, wherever ez was run
law anchor_url:
  for here: String
  for +a: String
  for +b: String
  {Path.anchor(here, a ++ ("://" ++ b)) == a ++ ("://" ++ b) : String}

# LAW: an absolute path is fetched as it is, wherever ez was run
law anchor_absolute:
  for here: String
  for +rest: String
  for e: {False{} == String.contains("/" ++ rest, "://") : Bool}
  {Path.anchor(here, "/" ++ rest) == "/" ++ rest : String}

# LAW: a relative path, which the ledger keeps as it was given, is taken from
# the directory ez runs in, the project's, and not from the work directory or
# the repository top git would read it from
law anchor_relative:
  for +here: String
  for +path: String
  for eu: {False{} == String.contains(path, "://") : Bool}
  for ea: {False{} == String.starts_with(path, "/") : Bool}
  for eg: {False{} == String.starts_with(path, "git@") : Bool}
  {Path.anchor(here, path) == Path.join(here, path) : String}
