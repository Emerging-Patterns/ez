# what an add's plan writes: the edited ledger, its effects, and the lock
# joined after it
#
# The plan is `plan.v(decide(w), w)`: `decide` settles what is refused or
# still asked before the walk, and on `Go` the plan is `made`, which seals
# the effects of the walk with how it ends (`outcome.k`). A sealed plan that
# refuses has no effect, so the refusal law is two case splits. A plan that
# does not refuse is therefore `Plan{effects.k(walked(w), w), Success}` with
# `outcome.k` a success (`succeeds`), and every law about what an add writes
# is a law about `effects.k`, whose one arm that is not empty is the walk's
# package.
import Base
import ../../src/check/eq.bend as Eq
import ../../src/relock/relock.bend as R
import ../../src/lock/plan.bend as P
import ../../src/pkg/pkg.bend as K
import ../../src/pkg/path.bend as Path
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/pub/world.bend as PW
import ../../src/pub/plan.bend as PP
import ../../src/git/git.bend as Git
import ../../src/add/world.bend as A
import ../../src/add/plan.bend as AP
import ../../src/add/hub.bend as H
import ../../laws/AddDependencyIdempotent.bend as L1
import ../../laws/PublishAgreesWithBend.bend as L2
import ./LockPlannerFacts.bend as M1
import ./PlanEffectFacts.bend as M2

# LAW: a lock that succeeds after an edit that succeeded runs the edit's
# effects, the notes and the lock's effects, in that order
law lock_effects:
  for l: P.Plan
  for +e: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for ok: {R.refuses(R.join.lock(l, e, n, t)) == False{} : Bool}
  {P.effects(R.join.lock(l, e, n, t)) == List.append(&2, P.Effect, P.effects(e),
    List.append(&2, P.Effect, n, P.effects(l))) : List<&2, P.Effect>}

def lock_effects(l, e, n, t, ok):
  match l:
    case P.Plan{es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{why}:
          Eq.bit.absurd2(&2, {P.effects(R.join.lock(P.Plan{es, P.Refused{why}}, e, n, t))
            == List.append(&2, P.Effect, P.effects(e),
              List.append(&2, P.Effect, n, P.effects(P.Plan{es, P.Refused{why}})))
            : List<&2, P.Effect>}, ok)

law edit_effects:
  for b: Bool
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for ok: {R.refuses(R.join.edit(b, e, l, n, t)) == False{} : Bool}
  {P.effects(R.join.edit(b, e, l, n, t)) == List.append(&2, P.Effect, P.effects(e),
    List.append(&2, P.Effect, n, P.effects(l))) : List<&2, P.Effect>}

def edit_effects(b, e, l, n, t, ok):
  match b:
    case True{}:
      Eq.bit.absurd2(&2, {P.effects(R.join.edit(True{}, e, l, n, t))
        == List.append(&2, P.Effect, P.effects(e), List.append(&2, P.Effect, n, P.effects(l)))
        : List<&2, P.Effect>}, ok)
    case False{}:
      lock_effects(l, e, n, t, ok)

# LAW: a joined plan that succeeds runs the edit's effects, the notes, and the
# lock's effects
law join_effects:
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for ok: {R.refuses(R.join(e, l, n, t)) == False{} : Bool}
  {P.effects(R.join(e, l, n, t)) == List.append(&2, P.Effect, P.effects(e),
    List.append(&2, P.Effect, n, P.effects(l))) : List<&2, P.Effect>}

def join_effects(e, l, n, t, ok):
  edit_effects(R.refuses(e), e, l, n, t, ok)

# LAW: a lock that refuses refuses the joined plan, whatever the edit did
law edit_refuses_lock:
  for b: Bool
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(l) == True{} : Bool}
  {R.refuses(R.join.edit(b, e, l, n, t)) == True{} : Bool}

def edit_refuses_lock(b, e, l, n, t, r):
  match b:
    case True{}:
      {==}
    case False{}:
      match l:
        case P.Plan{es, o}:
          match o:
            case P.Success{}:
              Eq.bit.absurd(&2, {R.refuses(R.join.edit(False{}, e, P.Plan{es, P.Success{}}, n, t))
                == True{} : Bool}, r)
            case P.Refused{_why}:
              {==}

law join_refuses_lock:
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(l) == True{} : Bool}
  {R.refuses(R.join(e, l, n, t)) == True{} : Bool}

def join_refuses_lock(e, l, n, t, r):
  edit_refuses_lock(R.refuses(e), e, l, n, t, r)

# ---------------------------------------------------------------------------
# what a publish that succeeds says, and that nothing is written

law said_made:
  for v: PP.Verdict
  for +w: PW.World
  for ok: {PP.succeeds.plan(PP.plan.v(v, w)) == True{} : Bool}
  {P.said(PP.plan.v(v, w)) == [PP.hash(w), Git.import.line(PP.called(w), PP.at(w))]
    : List<&2, String>}

def said_made(v, w, ok):
  match v:
    case PP.Go{}:
      {==}
    case PP.Pending{asks}:
      Eq.bit.absurd(&2, {P.said(PP.plan.v(PP.Pending{asks}, w))
        == [PP.hash(w), Git.import.line(PP.called(w), PP.at(w))] : List<&2, String>}, ok)
    case PP.Stop{why}:
      Eq.bit.absurd(&2, {P.said(PP.plan.v(PP.Stop{why}, w))
        == [PP.hash(w), Git.import.line(PP.called(w), PP.at(w))] : List<&2, String>}, ok)

def L2.pub_reports_ours(w, ok):
  said_made(PP.decide(w), w, ok)

# ---------------------------------------------------------------------------
# an add that does not refuse

# LAW: a verdict whose plan does not refuse is `Go`, and its plan is `made`
law plan_made_add:
  for v: AP.Verdict
  for +w: A.World
  for ok: {AP.refuses.plan(AP.plan.v(v, w)) == False{} : Bool}
  {AP.plan.v(v, w) == AP.made(AP.walked(w), w) : P.Plan}

def plan_made_add(v, w, ok):
  match v:
    case AP.Go{}:
      {==}
    case AP.Pending{qs}:
      Eq.bit.absurd2(&2, {AP.plan.v(AP.Pending{qs}, w) == AP.made(AP.walked(w), w) : P.Plan}, ok)
    case AP.Stop{why}:
      Eq.bit.absurd2(&2, {AP.plan.v(AP.Stop{why}, w) == AP.made(AP.walked(w), w) : P.Plan}, ok)

# LAW: a sealed plan that does not refuse is its effects, ending in success
law seal_success:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for ok: {AP.refuses.plan(AP.seal(es, o)) == False{} : Bool}
  {AP.seal(es, o) == P.Plan{es, P.Success{}} : P.Plan}

def seal_success(_es, o, ok):
  match o:
    case P.Success{}:
      {==}
    case P.Refused{why}:
      Eq.bit.absurd2(&2, {AP.seal(_es, P.Refused{why}) == P.Plan{_es, P.Success{}} : P.Plan},
        ok)

# LAW: and its outcome is a success
law seal_outcome:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for ok: {AP.refuses.plan(AP.seal(es, o)) == False{} : Bool}
  {o == P.Success{} : P.Outcome}

def seal_outcome(_es, o, ok):
  match o:
    case P.Success{}:
      {==}
    case P.Refused{why}:
      Eq.bit.absurd2(&2, {P.Refused{why} == P.Success{} : P.Outcome}, ok)

# LAW: an add that does not refuse made a plan that does not refuse
law made_ok:
  for +w: A.World
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.refuses.plan(AP.made(AP.walked(w), w)) == False{} : Bool}

def made_ok(w, ok):
  Equal.trans(Bool, AP.refuses.plan(AP.made(AP.walked(w), w)),
    AP.refuses.plan(AP.plan(w)), False{},
    Equal.cong(P.Plan, Bool, pl => AP.refuses.plan(pl),
      AP.made(AP.walked(w), w), AP.plan(w),
      Equal.sym(P.Plan, AP.plan(w), AP.made(AP.walked(w), w),
        plan_made_add(AP.decide(w), w, ok))),
    ok)

# LAW: an add that does not refuse runs the effects of its walk
law succeeds:
  for +w: A.World
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.plan(w) == P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}} : P.Plan}

def succeeds(w, ok):
  Equal.trans(P.Plan, AP.plan(w), AP.made(AP.walked(w), w),
    P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    plan_made_add(AP.decide(w), w, ok),
    seal_success(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w),
      made_ok(w, ok)))

# LAW: and its walk ends in success
law won:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {AP.outcome.k(AP.walked(w), w) == P.Success{} : P.Outcome}

def won(w, ok):
  seal_outcome(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w),
    made_ok(w, ok))

# LAW: a walk that made no package never ends in success
law asks_loses:
  for got: Maybe<&2, String>
  for +at: String
  for +w: A.World
  {M1.win(AP.outcome.entry(got, K.Asks{at}, w)) == False{} : Bool}

def asks_loses(got, _at, _w):
  match got:
    case None{}:
      {==}
    case Some{_t}:
      {==}

law refused_loses:
  for got: Maybe<&2, String>
  for +why: String
  for +w: A.World
  {M1.win(AP.outcome.entry(got, K.Refused{why}, w)) == False{} : Bool}

def refused_loses(got, _why, _w):
  match got:
    case None{}:
      {==}
    case Some{_t}:
      {==}

# LAW: a walk that ends in success records the dependency its package makes
law added_is:
  for k: K.Walked
  for +w: A.World
  for s: {AP.outcome.k(k, w) == P.Success{} : P.Outcome}
  {AP.added.k(k, w) == AP.dep.of(M1.wh(k), M2.wr(k), w) : M.Dep}

def added_is(k, w, s):
  match k:
    case K.Walked{_h, _r, _fs, _ss}:
      {==}
    case K.Asks{at}:
      Eq.bit.absurd(&2, {AP.added.k(K.Asks{at}, w) == AP.dep.of("", "", w) : M.Dep},
        Equal.trans(Bool, False{}, M1.win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, M1.win(AP.outcome.k(K.Asks{at}, w)), False{},
            asks_loses(M1.got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => M1.win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {AP.added.k(K.Refused{why}, w) == AP.dep.of("", "", w) : M.Dep},
        Equal.trans(Bool, False{}, M1.win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, M1.win(AP.outcome.k(K.Refused{why}, w)), False{},
            refused_loses(M1.got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => M1.win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

# LAW: an add that does not refuse records its walk's package
law added_ok:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {AP.added(w) == AP.dep.of(M1.wh(AP.walked(w)), M2.wr(AP.walked(w)), w) : M.Dep}

def added_ok(w, ok):
  added_is(AP.walked(w), w, won(w, ok))

# ---------------------------------------------------------------------------
# what an add writes

# a walk's files and sums, none for no package
def wf(k: K.Walked) -> List<&2, K.Source>:
  match k:
    case K.Walked{_h, _r, fs, _ss}:
      fs
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# LAW: a walk that ends in success has the effects its package makes
law effects_is:
  for k: K.Walked
  for +w: A.World
  for s: {AP.outcome.k(k, w) == P.Success{} : P.Outcome}
  {AP.effects.k(k, w) == AP.effects.of(AP.dep.of(M1.wh(k), M2.wr(k), w), M1.wh(k), AP.at.of(M2.wr(k), w),
    wf(k), M2.ws(k), A.manifest.of(A.read(w)), w) : List<&2, P.Effect>}

def effects_is(k, w, s):
  match k:
    case K.Walked{_h, _r, _fs, _ss}:
      {==}
    case K.Asks{at}:
      Eq.bit.absurd(&2, {AP.effects.k(K.Asks{at}, w) == AP.effects.of(AP.dep.of("", "", w),
        "", AP.at.of("", w), [], [], A.manifest.of(A.read(w)), w) : List<&2, P.Effect>},
        Equal.trans(Bool, False{}, M1.win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, M1.win(AP.outcome.k(K.Asks{at}, w)), False{},
            asks_loses(M1.got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => M1.win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {AP.effects.k(K.Refused{why}, w) == AP.effects.of(AP.dep.of("", "", w),
        "", AP.at.of("", w), [], [], A.manifest.of(A.read(w)), w) : List<&2, P.Effect>},
        Equal.trans(Bool, False{}, M1.win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, M1.win(AP.outcome.k(K.Refused{why}, w)), False{},
            refused_loses(M1.got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => M1.win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

# LAW: the lines a person is told write nothing
law says_keep:
  for c: Bool
  for +a: String
  for +b: String
  for +p: String
  {P.put.in(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{b}, P.Say{a}]), p)
    == P.Kept{} : P.Wrote}

def says_keep(c, _a, _b, _p):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: nor do the committed trees removed ahead of them
law drops_keep_add:
  for gs: List<&2, String>
  for rest: List<&2, P.Effect>
  for +p: String
  for e: {P.put.in(rest, p) == P.Kept{} : P.Wrote}
  {P.put.in(P.drops.of(gs, rest), p) == P.Kept{} : P.Wrote}

def drops_keep_add(gs, rest, p, e):
  match gs:
    case []:
      e
    case _h <> t:
      drops_keep_add(t, rest, p, e)

# LAW: so what follows the `.gitignore` write writes nothing
law tail_keep:
  for +h: String
  for +a: String
  for +w: A.World
  for gs: List<&2, String>
  for +p: String
  {P.put.in(P.drops.of(gs, AP.says(h, a, w)), p) == P.Kept{} : P.Wrote}

def tail_keep(h, a, w, gs, p):
  drops_keep_add(gs, AP.says(h, a, w), p,
    says_keep(String.is_empty(AP.tag(w)), Git.import.line(h, a),
      AP.tag(w) ++ " is " ++ AP.rev(w), p))

# LAW: and nothing after the ledger's write writes ez.toml
law ignore_keeps_ledger_add:
  for b: Bool
  for +next: String
  for gs: List<&2, String>
  for +h: String
  for +a: String
  for +w: A.World
  {P.put.in(AP.ignore.put(b, next, P.drops.of(gs, AP.says(h, a, w))), "ez.toml") == P.Kept{}
    : P.Wrote}

def ignore_keeps_ledger_add(b, next, gs, h, a, w):
  match b:
    case True{}:
      tail_keep(h, a, w, gs, "ez.toml")
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(gs, AP.says(h, a, w)), "ez.toml"), P.Kept{},
        tail_keep(h, a, w, gs, "ez.toml"))
        : {P.put.one(P.Write{".gitignore", next}, "ez.toml", _) == P.Kept{} : P.Wrote}
      {==}

# LAW: a write of ez.toml that nothing after it overwrites is what it leaves
law write_then_keep:
  for +text: String
  for tail: List<&2, P.Effect>
  for e: {P.put.in(tail, "ez.toml") == P.Kept{} : P.Wrote}
  {P.put.in(P.Write{"ez.toml", text} <> tail, "ez.toml") == P.Put{text} : P.Wrote}

def write_then_keep(text, tail, e):
  %Equal.sym(P.Wrote, P.put.in(tail, "ez.toml"), P.Kept{}, e)
    : {P.put.one(P.Write{"ez.toml", text}, "ez.toml", _) == P.Put{text} : P.Wrote}
  {==}

# LAW: the effects of a package leave ez.toml holding the edited ledger
law edits_of:
  for +d: M.Dep
  for +h: String
  for +a: String
  for fs: List<&2, K.Source>
  for ss: List<&2, K.Item>
  for +m: M.Manifest
  for +w: A.World
  {P.put.in(AP.effects.of(d, h, a, fs, ss, m, w), "ez.toml")
    == P.Put{Rend.show(Rend.add.keep(m, d))} : P.Wrote}

def edits_of(d, h, a, _fs, _ss, m, w):
  write_then_keep(Rend.show(Rend.add.keep(m, d)),
    AP.ignore.put(String.eq(M1.nxt(d, m, w), A.ignore(w)), M1.nxt(d, m, w),
      P.drops.of(M1.gss(d, h, m), AP.says(h, a, w))),
    ignore_keeps_ledger_add(String.eq(M1.nxt(d, m, w), A.ignore(w)), M1.nxt(d, m, w), M1.gss(d, h, m),
      h, a, w))

def eff(+w: A.World) -> List<&2, P.Effect>:
  AP.effects.of(M1.dd(w), M1.wh(AP.walked(w)), M2.aa(w), wf(AP.walked(w)), M2.ws(AP.walked(w)),
    A.manifest.of(A.read(w)), w)

# the manifest of a ledger that read, as the premise gives it
def good_m(
  +w: A.World,
  +m: M.Manifest,
  good: {A.read(w) == M.Good{m} : M.Read}
) -> {A.manifest.of(A.read(w)) == m : M.Manifest}:
  Equal.cong(M.Read, M.Manifest, r => A.manifest.of(r), A.read(w), M.Good{m}, good)

def L1.add_edits_ledger(w, m, good, ok):
  %Equal.sym(P.Plan, AP.plan(w), P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    succeeds(w, ok))
    : {P.put.plan(_, "ez.toml") == P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))} : P.Wrote}
  %Equal.sym(M.Dep, AP.added(w), M1.dd(w), added_ok(w, ok))
    : {P.put.in(AP.effects.k(AP.walked(w), w), "ez.toml") == P.Put{Rend.show(Rend.add.keep(m,
      _))} : P.Wrote}
  %Equal.sym(List<&2, P.Effect>, AP.effects.k(AP.walked(w), w), eff(w),
    effects_is(AP.walked(w), w, won(w, ok)))
    : {P.put.in(_, "ez.toml") == P.Put{Rend.show(Rend.add.keep(m, M1.dd(w)))} : P.Wrote}
  %good_m(w, m, good)
    : {P.put.in(eff(w), "ez.toml") == P.Put{Rend.show(Rend.add.keep(_, M1.dd(w)))} : P.Wrote}
  edits_of(M1.dd(w), M1.wh(AP.walked(w)), M2.aa(w), wf(AP.walked(w)), M2.ws(AP.walked(w)),
    A.manifest.of(A.read(w)), w)

# LAW: the lines a hub add tells write nothing
law hsays_keep:
  for c: Bool
  for +a: String
  for +b: String
  for +p: String
  {P.put.in(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{a}, P.Say{b}]), p)
    == P.Kept{} : P.Wrote}

def hsays_keep(c, _a, _b, _p):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: nor does anything after the ledger's write, `.gitignore` included
law hignore_keeps_ledger:
  for b: Bool
  for +next: String
  for +h: String
  for +e: String
  for +w: A.World
  {P.put.in(H.ignore.put(b, next, H.says(h, e, w)), "ez.toml") == P.Kept{} : P.Wrote}

def hignore_keeps_ledger(b, next, h, e, w):
  match b:
    case True{}:
      hsays_keep(String.is_empty(e), A.target(w) ++ " is " ++ h,
        Git.import.line(A.target(w), Path.norm(e)), "ez.toml")
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(H.says(h, e, w), "ez.toml"), P.Kept{},
        hsays_keep(String.is_empty(e), A.target(w) ++ " is " ++ h,
          Git.import.line(A.target(w), Path.norm(e)), "ez.toml"))
        : {P.put.one(P.Write{".gitignore", next}, "ez.toml", _) == P.Kept{} : P.Wrote}
      {==}

def L1.add_named_edits_ledger(w, m, good, ok):
  %Equal.sym(P.Plan, H.plan(w), P.Plan{M1.heff(w), P.Success{}}, M1.hsucceeds(w, ok))
    : {P.put.plan(_, "ez.toml") == P.Put{Rend.show(Rend.add.keep(m, H.added(w)))} : P.Wrote}
  %good_m(w, m, good)
    : {P.put.in(M1.heff(w), "ez.toml") == P.Put{Rend.show(Rend.add.keep(_, H.added(w)))}
      : P.Wrote}
  write_then_keep(Rend.show(Rend.add.keep(A.manifest.of(A.read(w)), H.added(w))),
    H.ignore.put(M1.hsame(w), M1.hnext(w), H.says(H.hash(w), M.dep.entry(H.added(w)), w)),
    hignore_keeps_ledger(M1.hsame(w), M1.hnext(w), H.hash(w), M.dep.entry(H.added(w)), w))
