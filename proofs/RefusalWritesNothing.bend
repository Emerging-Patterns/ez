# proofs of laws/RefusalWritesNothing.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
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
import ../laws/PublishNeedsDepsOnHub.bend as L1
import ../laws/RefusalWritesNothing.bend as Laws
import ../laws/ToolBuiltFileChosen.bend as L2
import ./lemmas/JoinedPlanRefusals.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2
import ./lemmas/PlannerStages.bend as M3

law quiet_pub:
  for v: PP.Verdict
  for +w: PW.World
  {P.writes(PP.plan.v(v, w)) == False{} : Bool}

def quiet_pub(v, _w):
  match v:
    case PP.Go{}:
      {==}
    case PP.Pending{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def Laws.pub_refusal_writes_nothing(w, _r):
  quiet_pub(PP.decide(w), w)

def Laws.pub_misnamed_writes_nothing(here, text, rs, n, e, b, h, pa, pv, ds, ts, why, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.plan.v(PP.decide.led(PP.led.read(_), PW.World{here, Some{text}, rs}), PW.World{here, Some{text},
      rs}) == P.Plan{[], P.Refused{why}} : P.Plan}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.Unnamed{why}, u)
    : {PP.plan.v(PP.decide.led(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _), PW.World{here,
      Some{text}, rs}), PW.World{here, Some{text}, rs}) == P.Plan{[], P.Refused{why}} : P.Plan}
  {==}

# LAW: a verdict that sends nothing has a plan with no effect
law unsent_quiet:
  for v: PP.Verdict
  for +w: PW.World
  for r: {PP.sends.v(v) == False{} : Bool}
  {P.effects(PP.plan.v(v, w)) == [] : List<&2, P.Effect>}

def unsent_quiet(v, w, r):
  match v:
    case PP.Go{}:
      Eq.bit.absurd2(&2, {P.effects(PP.plan.v(PP.Go{}, w)) == [] : List<&2, P.Effect>}, r)
    case PP.Pending{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def Laws.pub_offhub_writes_nothing(w, why, e):
  unsent_quiet(PP.decide(w), w, L1.pub_offhub_sends_nothing(w, why, e))

# ---------------------------------------------------------------------------
# refusals

# LAW: a sealed plan that refuses writes nothing
law seal_quiet_add:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for r: {AP.refuses.plan(AP.seal(es, o)) == True{} : Bool}
  {P.writes(AP.seal(es, o)) == False{} : Bool}

def seal_quiet_add(es, o, r):
  match o:
    case P.Success{}:
      Eq.bit.absurd(&2, {P.writes(AP.seal(es, P.Success{})) == False{} : Bool}, r)
    case P.Refused{_why}:
      {==}

# LAW: nor does any plan for a verdict that refuses
law plan_quiet:
  for v: AP.Verdict
  for +w: A.World
  for r: {AP.refuses.plan(AP.plan.v(v, w)) == True{} : Bool}
  {P.writes(AP.plan.v(v, w)) == False{} : Bool}

def plan_quiet(v, w, r):
  match v:
    case AP.Go{}:
      seal_quiet_add(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), r)
    case AP.Pending{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

# ---------------------------------------------------------------------------
# a hub package's `<name>@<version>` (`H.plan`)
#
# The hub plan is `H.plan.v(H.decide(w), w)`. `H.decide` walks the ledger,
# the refusals the ledger decides, the hub's answer for the name, and the
# package it serves for that hash; each law about where it lands is proved by
# a walk down those arms, the arms the premises rule out closing at once. On
# `Go` the plan is `H.made`, which seals the effects of the package with how
# it ends.

# LAW: the two readings of whether a plan refuses are one
law refuses_same:
  for pl: P.Plan
  {AP.refuses.plan(pl) == H.refuses.plan(pl) : Bool}

def refuses_same(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

# LAW: a sealed hub plan that refuses writes nothing
law hseal_quiet:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for r: {H.refuses.plan(H.seal(es, o)) == True{} : Bool}
  {P.writes(H.seal(es, o)) == False{} : Bool}

def hseal_quiet(es, o, r):
  match o:
    case P.Success{}:
      Eq.bit.absurd(&2, {P.writes(H.seal(es, P.Success{})) == False{} : Bool}, r)
    case P.Refused{_why}:
      {==}

# LAW: nor does any hub plan for a verdict that refuses
law hplan_quiet:
  for v: H.Verdict
  for +w: A.World
  for r: {H.refuses.plan(H.plan.v(v, w)) == True{} : Bool}
  {P.writes(H.plan.v(v, w)) == False{} : Bool}

def hplan_quiet(v, w, r):
  match v:
    case H.Go{+h, +fs, +ss}:
      hseal_quiet(H.effects.of(H.dep.of(h, fs, w), h, W.laid(fs, ss),
        A.manifest.of(A.read(w)), w), H.outcome.of(h, fs, w), r)
    case H.Pending{_asks}:
      {==}
    case H.Stop{_why}:
      {==}

def Laws.add_named_refusal_writes_nothing(w, r):
  hplan_quiet(H.decide(w), w, r)

# LAW: and that arm stops whenever the name's arm does
law hearly_stops:
  for b: Bool
  for +why: String
  for +w: A.World
  for g: {M3.hstops(H.decide.name(H.heard(A.hubs(w), A.target(w)), w)) == True{} : Bool}
  {M3.hstops(H.decide.early(b, why, w)) == True{} : Bool}

def hearly_stops(b, _why, _w, g):
  match b:
    case True{}:
      g
    case False{}:
      {==}

# LAW: a name the hub has no package for stops the add
law hmiss_stops:
  for +w: A.World
  for why: String
  for miss: {H.heard(A.hubs(w), A.target(w)) == Some{W.Miss{why}} : Maybe<&2, W.Answer>}
  {M3.hstops(H.decide.name(H.heard(A.hubs(w), A.target(w)), w)) == True{} : Bool}

def hmiss_stops(w, why, miss):
  %Equal.sym(Maybe<&2, W.Answer>, H.heard(A.hubs(w), A.target(w)), Some{W.Miss{why}}, miss)
    : {M3.hstops(H.decide.name(_, w)) == True{} : Bool}
  {==}

def Laws.add_named_refuses_unknown(w, why, miss):
  M3.hstops_refuses(H.decide(w), w,
    M3.hread_stops(A.read(w), w,
      hearly_stops(String.is_empty(H.early(w)), H.early(w), w, hmiss_stops(w, why, miss))))

# LAW: an answer that is no `0x` name stops the add
law hbad_hash_stops:
  for ok: Bool
  for +hash: String
  for +w: A.World
  for e: {ok == False{} : Bool}
  {M3.hstops(H.decide.hash(ok, hash, w)) == True{} : Bool}

def hbad_hash_stops(ok, hash, w, e):
  match ok:
    case True{}:
      Eq.bit.absurd2(&2, {M3.hstops(H.decide.hash(True{}, hash, w)) == True{} : Bool}, e)
    case False{}:
      {==}

def Laws.add_named_refuses_unhashed(w, text, said, bad):
  M3.hstops_refuses(H.decide(w), w,
    M3.hread_stops(A.read(w), w,
      hearly_stops(String.is_empty(H.early(w)), H.early(w), w,
        Equal.trans(Bool, M3.hstops(H.decide.name(H.heard(A.hubs(w), A.target(w)), w)),
          M3.hstops(H.decide.hash(L.hash.ok(String.trim(text)), String.trim(text), w)), True{},
          Equal.cong(Maybe<&2, W.Answer>, Bool, g => M3.hstops(H.decide.name(g, w)),
            H.heard(A.hubs(w), A.target(w)), Some{W.Said{text}}, said),
          hbad_hash_stops(L.hash.ok(String.trim(text)), String.trim(text), w, bad)))))

# LAW: a package whose manifest does not hash to its name stops the add,
# however it arrived
law hbody_stops:
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for bad: {Web.matches(L.want(hash), manifest) == False{} : Bool}
  {M3.hstops(H.decide.body(W.hub.how(how, hash, manifest, ss), hash)) == True{} : Bool}

def hbody_stops(how, hash, manifest, ss, bad):
  match how:
    case W.Lib{}:
      {==}
    case W.Clone{_got}:
      {==}
    case W.Served{}:
      %Equal.sym(Bool, Web.matches(L.want(hash), manifest), False{}, bad)
        : {M3.hstops(H.decide.body(W.body.named(_, hash, manifest, ss), hash)) == True{} : Bool}
      {==}

# LAW: so does a `0x` name the hub answered whose package is that one
law hgot_stops:
  for ok: Bool
  for +hash: String
  for +w: A.World
  for how: W.How
  for +manifest: String
  for +ss: List<&2, String>
  for got: {H.heard(A.hubs(w), hash) == Some{W.Got{how, manifest, ss}} : Maybe<&2, W.Answer>}
  for bad: {Web.matches(L.want(hash), manifest) == False{} : Bool}
  {M3.hstops(H.decide.hash(ok, hash, w)) == True{} : Bool}

def hgot_stops(ok, hash, w, how, manifest, ss, got, bad):
  match ok:
    case True{}:
      %Equal.sym(Maybe<&2, W.Answer>, H.heard(A.hubs(w), hash), Some{W.Got{how, manifest, ss}},
        got)
        : {M3.hstops(H.decide.pkg(_, hash, w)) == True{} : Bool}
      hbody_stops(how, hash, manifest, ss, bad)
    case False{}:
      {==}

def Laws.add_named_refuses_manifest(w, text, said, how, manifest, ss, got, bad):
  M3.hstops_refuses(H.decide(w), w,
    M3.hread_stops(A.read(w), w,
      hearly_stops(String.is_empty(H.early(w)), H.early(w), w,
        Equal.trans(Bool, M3.hstops(H.decide.name(H.heard(A.hubs(w), A.target(w)), w)),
          M3.hstops(H.decide.hash(L.hash.ok(String.trim(text)), String.trim(text), w)), True{},
          Equal.cong(Maybe<&2, W.Answer>, Bool, g => M3.hstops(H.decide.name(g, w)),
            H.heard(A.hubs(w), A.target(w)), Some{W.Said{text}}, said),
          hgot_stops(L.hash.ok(String.trim(text)), String.trim(text), w, how, manifest, ss,
            got, bad)))))

# ---------------------------------------------------------------------------
# the command: whichever planner runs

# LAW: the command's plan refuses without effect, whichever planner runs
law command_quiet:
  for b: Bool
  for +w: A.World
  for r: {AP.refuses.plan(AP.command.of(b, w)) == True{} : Bool}
  {P.writes(AP.command.of(b, w)) == False{} : Bool}

def command_quiet(b, w, r):
  match b:
    case True{}:
      hplan_quiet(H.decide(w), w,
        Equal.trans(Bool, H.refuses.plan(H.plan(w)), AP.refuses.plan(H.plan(w)), True{},
          Equal.sym(Bool, AP.refuses.plan(H.plan(w)), H.refuses.plan(H.plan(w)),
            refuses_same(H.plan(w))), r))
    case False{}:
      plan_quiet(AP.decide(w), w, r)

def Laws.add_refusal_writes_nothing(w, r):
  command_quiet(A.named(w), w, r)

def Laws.add_whole_refusal_writes_nothing(w, r):
  match w:
    case AR.World{+a, +listing, +locks}:
      M1.join_quiet(AP.command(a), AR.lock(AR.World{a, listing, locks}),
        AR.notes(AR.World{a, listing, locks}), AR.tail(a), r)

# LAW: a new project's plan that refuses writes nothing
law new_quiet:
  for +ok: Bool
  for +name: String
  for +at: String
  for +desc: String
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  for +r: {IP.refuses.plan(IP.plan.new(ok, name, at, desc, ig, mn, lb)) == True{} : Bool}
  {P.writes(IP.plan.new(ok, name, at, desc, ig, mn, lb)) == False{} : Bool}

def new_quiet(ok, name, at, desc, ig, mn, lb, r):
  match ok:
    case True{}:
      Eq.bit.absurd(&2, {P.writes(IP.plan.new(True{}, name, at, desc, ig, mn, lb)) == False{} : Bool}, r)
    case False{}:
      {==}

# A ledger that is there is the arm with no effect; one that is not refuses
# only when the project does not fit, which has no effect either.
def Laws.init_refusal_writes_nothing(w, r):
  match w:
    case IP.World{n, e, d, led, ig, mn, lb}:
      match led:
        case Some{s}:
          {==}
        case None{}:
          new_quiet(IP.fits(IP.name.or(n), IP.entry.or(e), d),
            IP.name.or(n), IP.entry.or(e), d, ig, mn, lb, r)

# LAW: a plan that refuses no ledger it read has no effect when the name is
# absent, and ends in success when it is there
law refused_has:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for r: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == True{} : Bool}
  {P.writes(RP.plan.has(h, m, name, ignore)) == False{} : Bool}

def refused_has(h, m, name, ignore, r):
  match h:
    case True{}:
      Eq.bit.absurd(&2, {P.writes(RP.plan.has(True{}, m, name, ignore)) == False{}
        : Bool}, r)
    case False{}:
      {==}

# LAW: the same for any read of the ledger
law refused_read:
  for led: M.Read
  for +name: String
  for +ignore: String
  for r: {RP.refuses.plan(RP.plan.read(led, name, ignore)) == True{} : Bool}
  {P.writes(RP.plan.read(led, name, ignore)) == False{} : Bool}

def refused_read(led, name, ignore, r):
  match led:
    case M.Bad{_why}:
      {==}
    case M.Good{+m}:
      refused_has(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))), m, name, ignore, r)

def Laws.remove_refusal_writes_nothing(w, r):
  match w:
    case RP.World{+n, l, +ig}:
      refused_read(RP.read.of(l), n, ig, r)

def Laws.remove_whole_refusal_writes_nothing(w, r):
  match w:
    case RR.World{+rm, +here, +listing, +locks}:
      M1.join_quiet(RP.plan(rm), RR.lock(RR.World{rm, here, listing, locks}), [], RR.tail(), r)

# ---------------------------------------------------------------------------
# refusals

# LAW: a verdict whose plan refuses writes nothing
law quiet_tool:
  for v: TP.Verdict
  for +w: TW.World
  for r: {TP.refuses.plan(TP.plan.v(v, w)) == True{} : Bool}
  {TP.writes(TP.plan.v(v, w)) == False{} : Bool}

def quiet_tool(v, w, r):
  match v:
    case TP.Go{}:
      Eq.bit.absurd(&2, {TP.writes(TP.plan.v(TP.Go{}, w)) == False{} : Bool}, r)
    case TP.Pending{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}

def Laws.tool_refusal_writes_nothing(w, r):
  quiet_tool(TP.decide(w), w, r)

# LAW: a sync that refuses names nothing to install
law sync_quiet:
  for s: TP.Sync
  for r: {TP.sync.refuses(s) == True{} : Bool}
  {TP.sync.names(s) == [] : List<&2, String>}

def sync_quiet(s, r):
  match s:
    case TP.Sync{ns}:
      Eq.bit.absurd(&2, {TP.sync.names(TP.Sync{ns}) == [] : List<&2, String>}, r)
    case TP.SyncNo{_why}:
      {==}

def Laws.sync_refusal_installs_nothing(ledger, lock, r):
  sync_quiet(TP.sync(ledger, lock), r)

def Laws.tool_missing_entry_writes_nothing(w, miss):
  Laws.tool_refusal_writes_nothing(w, L2.tool_refuses_missing_entry(w, miss))
