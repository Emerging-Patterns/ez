# A command that refuses writes nothing: every file it would otherwise write
# or remove is left as it found it.
#
# also rests on: laws/AddWsRefusalWritesNothing.bend,
# laws/FetchRefusalWritesNothing.bend, laws/RemoveWsRefusalWritesNothing.bend
#
# This guarantee is proved for every command, each over the plan its planner
# makes. `ez lock`, plain or `--upgrade`: a World on which the planner
# refuses has a plan with no write, lay or remove effect, so it writes
# nothing, not the lock, ez.toml, `.gitignore`, a source or a tree. The
# upgrade's refusals (a pin off its history, a drift, a hub digest that does
# not match, an answer IO could not give, an unknown `--package`, a ledger
# model that is not renderable) and the lock's refusals after an upgrade are
# all such Worlds. `ez remove` and `ez init`: the same, for every World on
# which their planners refuse: no ledger, one that does not parse, a name it
# does not have, or a ledger left that is not renderable, for `ez remove`; a
# ledger that is there, a name or entry a ledger cannot carry, or a
# description holding a newline, for `ez init`. `ez add`: the same for every
# World on which its planner refuses, before a question (no ledger, one that
# does not parse, a target that names nothing, a `--rename` that is no key
# or a clash the ledger decides) or after (a ref the remote does not have,
# an entry the checkout lacks, a walk that refuses, a name `Named.why.as`
# objects to, a ledger that is not renderable), so a refused add lays no
# tree, not even in the cache (`add_refusal_writes_nothing`). `ez add
# <name>@<version>` is planned by `H.plan` (src/add/hub.bend), and the same
# holds of it: no ledger, one that does not parse, a key `Named.hub.why`
# objects to, a name the hub has no package for or answers with no `0x`
# name, a package whose manifest does not hash to that name, an entry the
# package lacks, or a ledger that is not renderable, and it lays no tree and
# no name's file (`add_named_refusal_writes_nothing`,
# `add_named_refuses_unknown`, `add_named_refuses_unhashed`,
# `add_named_refuses_manifest`, `add_named_refuses_clash`,
# `add_named_entry_absent`, `add_named_refuses_unrenderable`). `ez fetch`:
# the same for every World on which its planner refuses (no ledger, no lock,
# a package that could not be fetched, one whose files do not match the
# lock, leave the package or do not hash to its name, or one whose checkout
# does not weigh to the lock's narHash), so a refused fetch lays no tree,
# not one of a package that checked before the one that failed, and removes
# none already under BEND_LIB (`fetch_refusal_writes_nothing`). `ez tool
# run`, `install` and `upgrade`: the same for every World on which their
# planner refuses (nowhere to link, no cache root, a project ledger that
# does not parse, a target that names nothing or whose slug could leave the
# cache, a name the lock does not pin or pins at no commit, a checkout git
# could not give, a file to build that is not in the checkout, a package
# name that is not a TOML bare key, an ez project's build with no lock), so
# a refused tool command lays no checkout under the cache, builds nothing
# and links nothing (`tool_refusal_writes_nothing`, and
# `tool_missing_entry_writes_nothing` for a missing file); and `ez tool
# sync`, which refuses before it installs anything when the ledger does not
# parse or names a pin the lock lacks (`sync_refusal_installs_nothing`). `ez
# publish`: its plan writes no file at all, only the two lines a publish
# that agreed says, so a refused publish writes nothing
# (`pub_refusal_writes_nothing`), and one refused because a hub import is
# off the hub has a plan with no effect at all
# (`pub_offhub_writes_nothing`); and every refusal that can be decided
# before the upload is decided before it, so a refused publish sends nothing
# unless bend's own answer is what it refuses
# (laws/PublishNeedsCleanTree.bend, laws/PublishAgreesWithBend.bend,
# laws/PublishNeedsDepsOnHub.bend). A sync that goes on runs one install per
# pin, each its own plan, so a later install that refuses leaves the earlier
# ones installed, as `cargo install a b` does. A write the interpreter
# attempts and the system rejects is laws/ExitStatusSaysFailure.bend's, and
# what it leaves is trusted in src/ez/app.bend.
import Base
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/hub/hub.bend as Web
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/add/relock.bend as AR
import ../src/init/plan.bend as IP
import ../src/remove/plan.bend as RP
import ../src/remove/relock.bend as RR
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# LAW: `ez publish` that refuses writes nothing: its plan has no effect but
# the lines it says, and a refused one says none
law pub_refusal_writes_nothing:
  for +w: PW.World
  for r: {PP.refuses(w) == True{} : Bool}
  {P.writes(PP.plan(w)) == False{} : Bool}

# LAW: and its plan is that refusal and nothing else, so it writes nothing
law pub_misnamed_writes_nothing:
  for +here: String
  for +text: String
  for +rs: List<&2, PW.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +pa: String
  for +pv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +why: String
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.Unnamed{why} : PP.Named}
  {PP.plan(PW.World{here, Some{text}, rs}) == P.Plan{[], P.Refused{why}} : P.Plan}

# LAW: and its plan has no effect at all: it writes nothing and says nothing
# but why it refuses
law pub_offhub_writes_nothing:
  for +w: PW.World
  for +why: String
  for e: {PP.hubbed(w) == PP.OffHub{why} : PP.Hubbed}
  {P.effects(PP.plan(w)) == [] : List<&2, P.Effect>}

# LAW: `ez lock` that refuses, plain or `--upgrade`, writes, lays and removes
# nothing: not the lock, not ez.toml, `.gitignore` or a source, and no tree.
# Its plan has no effect at all; the reason is how it ends. An upgrade whose
# remote answers refuse it, or whose lock then refuses, is such a World.
law lock_refusal_writes_nothing:
  for +w: W.World
  for r: {P.refuses(w) == True{} : Bool}
  {P.writes(P.plan(w)) == False{} : Bool}

# LAW: `ez add` that refuses writes, lays and removes nothing: not ez.toml,
# not `.gitignore`, no tree under BEND_LIB or `.ez/lib`, no name's file. Its
# plan has no effect at all; the reason is how it ends. So a refused add
# fills no cache either.
law add_refusal_writes_nothing:
  for +w: A.World
  for r: {AP.refuses.command(w) == True{} : Bool}
  {P.writes(AP.command(w)) == False{} : Bool}

# ---------------------------------------------------------------------------
# a hub package's `<name>@<version>` (`H.plan`)

# LAW: `ez add <name>@<version>` that refuses writes, lays and removes
# nothing
law add_named_refusal_writes_nothing:
  for +w: A.World
  for r: {H.refuses(w) == True{} : Bool}
  {P.writes(H.plan(w)) == False{} : Bool}

# LAW: a name the hub has no package for is refused
law add_named_refuses_unknown:
  for +w: A.World
  for why: String
  for miss: {H.heard(A.hubs(w), A.target(w)) == Some{W.Miss{why}} : Maybe<&2, W.Answer>}
  {H.refuses(w) == True{} : Bool}

# LAW: and so is one it answers with anything but a `0x` name
law add_named_refuses_unhashed:
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  for bad: {L.hash.ok(String.trim(text)) == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: a package whose manifest does not hash to the name the hub answered
# is refused, never laid or recorded
law add_named_refuses_manifest:
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  for how: W.How
  for +manifest: String
  for ss: List<&2, String>
  for got: {H.heard(A.hubs(w), String.trim(text)) == Some{W.Got{how, manifest, ss}}
    : Maybe<&2, W.Answer>}
  for bad: {Web.matches(L.want(String.trim(text)), manifest) == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: `ez add` that refuses, the add or the lock after it, writes, lays and
# removes nothing
law add_whole_refusal_writes_nothing:
  for +w: AR.World
  for r: {AR.refuses(w) == True{} : Bool}
  {P.writes(AR.plan(w)) == False{} : Bool}

# LAW: `ez init` that refuses writes nothing: not ez.toml, not `.gitignore`,
# and no entry. Its plan has no effect at all; the reason is how it ends.
law init_refusal_writes_nothing:
  for +w: IP.World
  for r: {IP.refuses(w) == True{} : Bool}
  {P.writes(IP.plan(w)) == False{} : Bool}

# LAW: `ez remove` that refuses writes, lays and removes nothing: not
# ez.toml, not `.gitignore`, and no committed tree. Its plan has no effect at
# all; the reason is how it ends. No ledger, one that does not parse, and a
# name the ledger does not have are all such Worlds.
law remove_refusal_writes_nothing:
  for +w: RP.World
  for r: {RP.refuses(w) == True{} : Bool}
  {P.writes(RP.plan(w)) == False{} : Bool}

# LAW: `ez remove` that refuses, the remove or the lock after it, writes,
# lays and removes nothing
law remove_whole_refusal_writes_nothing:
  for +w: RR.World
  for r: {RR.refuses(w) == True{} : Bool}
  {P.writes(RR.plan(w)) == False{} : Bool}

# ---------------------------------------------------------------------------
# refusals

# LAW: a tool command that refuses writes nothing: no checkout laid under the
# cache, no binary built, no link. Its plan has no effect at all.
law tool_refusal_writes_nothing:
  for +w: TW.World
  for r: {TP.refuses(w) == True{} : Bool}
  {TP.writes(TP.plan(w)) == False{} : Bool}

# LAW: a file to build that is not in the checkout is refused, so it too
# leaves nothing behind
law tool_missing_entry_writes_nothing:
  for +w: TW.World
  for miss: {TP.present(w) == False{} : Bool}
  {TP.writes(TP.plan(w)) == False{} : Bool}

# LAW: `ez tool sync` that refuses installs nothing
law sync_refusal_installs_nothing:
  for +ledger: Maybe<&2, String>
  for +lock: Maybe<&2, String>
  for r: {TP.sync.refuses(TP.sync(ledger, lock)) == True{} : Bool}
  {TP.sync.names(TP.sync(ledger, lock)) == [] : List<&2, String>}
