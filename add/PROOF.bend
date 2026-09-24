# add: the proofs. `bend PROOF.bend` is the gate.
#
# The plan is `plan.v(decide(w), w)`: `decide` settles what is refused or
# still asked before the walk, and on `Go` the plan is `made`, which seals the
# effects of the walk with how it ends (`outcome.k`). A sealed plan that
# refuses has no effect, so the refusal law is two case splits. A plan that
# does not refuse is therefore `Plan{effects.k(walked(w), w), Success}` with
# `outcome.k` a success (`succeeds`), and every law about what an add writes
# is a law about `effects.k`, whose one arm that is not empty is the walk's
# package.
import Base
import ./world.bend as A
import ./plan.bend as AP
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/up.bend as Up
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/ignore.bend as I
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as Git
import ../ez/target.bend as Tgt
import ../ez/named.bend as Named
import ../sha/sha.bend as Sha
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../pkg/PROOF.bend as Pk
import ../manifest/LAWS.bend as ML
import ../manifest/PROOF.bend as MP
import ./LAWS.bend as Laws

# ---------------------------------------------------------------------------
# refusals

# LAW: a sealed plan that refuses writes nothing
law seal_quiet:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for r: {AP.refuses.plan(AP.seal(es, o)) == True{} : Bool}
  {P.writes(AP.seal(es, o)) == False{} : Bool}

def seal_quiet(es, o, r):
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
      seal_quiet(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), r)
    case AP.Wait{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

def Laws.add_refusal_writes_nothing(w, r):
  plan_quiet(AP.decide(w), w, r)

# No ledger reads as the `Bad` arm, which stops before anything is asked.
def Laws.add_needs_ledger(_a, _here, _home, _ignore, _rs):
  {==}

def Laws.add_needs_ledger_asks_nothing(_a, _here, _home, _ignore, _rs):
  {==}

# The read is rewritten to the `Bad` the premise gives, which stops.
def Laws.add_refuses_unread(a, here, home, s, ignore, rs, _why, bad):
  %bad : {AP.refuses.plan(AP.plan.v(AP.decide.read(_, A.World{a, here, home, Some{s},
    ignore, rs}), A.World{a, here, home, Some{s}, ignore, rs})) == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# an add that does not refuse

# LAW: a verdict whose plan does not refuse is `Go`, and its plan is `made`
law plan_made:
  for v: AP.Verdict
  for +w: A.World
  for ok: {AP.refuses.plan(AP.plan.v(v, w)) == False{} : Bool}
  {AP.plan.v(v, w) == AP.made(AP.walked(w), w) : P.Plan}

def plan_made(v, w, ok):
  match v:
    case AP.Go{}:
      {==}
    case AP.Wait{qs}:
      Eq.bit.absurd2(&2, {AP.plan.v(AP.Wait{qs}, w) == AP.made(AP.walked(w), w) : P.Plan}, ok)
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
        plan_made(AP.decide(w), w, ok))),
    ok)

# LAW: an add that does not refuse runs the effects of its walk
law succeeds:
  for +w: A.World
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.plan(w) == P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}} : P.Plan}

def succeeds(w, ok):
  Equal.trans(P.Plan, AP.plan(w), AP.made(AP.walked(w), w),
    P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    plan_made(AP.decide(w), w, ok),
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

# an outcome as a bit
def win(o: P.Outcome) -> Bool:
  match o:
    case P.Success{}:
      True{}
    case P.Refused{_why}:
      False{}

# LAW: a walk that made no package never ends in success
law asks_loses:
  for got: Maybe<&2, String>
  for +at: String
  for +w: A.World
  {win(AP.outcome.entry(got, K.Asks{at}, w)) == False{} : Bool}

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
  {win(AP.outcome.entry(got, K.Refused{why}, w)) == False{} : Bool}

def refused_loses(got, _why, _w):
  match got:
    case None{}:
      {==}
    case Some{_t}:
      {==}

# the entry lookup `outcome.k` turns on
def got(+w: A.World) -> Maybe<&2, String>:
  K.look(AP.files(w), Path.norm(AP.entry(w)))

# a walk's hash and root, "" for no package
def wh(k: K.Walked) -> String:
  match k:
    case K.Walked{h, _r, _fs, _ss}:
      h
    case K.Asks{_at}:
      ""
    case K.Refused{_why}:
      ""

def wr(k: K.Walked) -> String:
  match k:
    case K.Walked{_h, r, _fs, _ss}:
      r
    case K.Asks{_at}:
      ""
    case K.Refused{_why}:
      ""

# LAW: a walk that ends in success records the dependency its package makes
law added_is:
  for k: K.Walked
  for +w: A.World
  for s: {AP.outcome.k(k, w) == P.Success{} : P.Outcome}
  {AP.added.k(k, w) == AP.dep.of(wh(k), wr(k), w) : M.Dep}

def added_is(k, w, s):
  match k:
    case K.Walked{_h, _r, _fs, _ss}:
      {==}
    case K.Asks{at}:
      Eq.bit.absurd(&2, {AP.added.k(K.Asks{at}, w) == AP.dep.of("", "", w) : M.Dep},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Asks{at}, w)), False{},
            asks_loses(got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {AP.added.k(K.Refused{why}, w) == AP.dep.of("", "", w) : M.Dep},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Refused{why}, w)), False{},
            refused_loses(got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

# LAW: an add that does not refuse records its walk's package
law added_ok:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {AP.added(w) == AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w) : M.Dep}

def added_ok(w, ok):
  added_is(AP.walked(w), w, won(w, ok))

def Laws.add_records_named(w, ok):
  Equal.cong(M.Dep, String, d => M.dep.name(d), AP.added(w),
    AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok))

def Laws.add_records_as_given(w, ok):
  Equal.cong(M.Dep, String, d => M.source.url(M.source.dep(d)), AP.added(w),
    AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok))

# The target's place is rewritten to the path the premise gives.
def Laws.add_path_as_given(w, p, e):
  %Equal.sym(Tgt.Place, Tgt.classify(A.target(w)), Tgt.Local{p}, e)
    : {A.url.of(_, A.home(w)) == Tgt.expand(A.home(w), p) : String}
  {==}

# LAW: with no ref, the tag recorded is the default one
law tag_default:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  {AP.tag(w) == AP.default.ref(w) : String}

def tag_default(w, none):
  %Equal.sym(String, A.ref(w), "", none) : {AP.tag.of(Git.is_rev(_), String.is_empty(_), w)
    == AP.default.ref(w) : String}
  {==}

def Laws.add_pins_chosen(w, none, ok):
  Equal.trans(String, M.source.tag(M.source.dep(AP.added(w))), AP.tag(w),
    AP.default.ref(w),
    Equal.cong(M.Dep, String, d => M.source.tag(M.source.dep(d)), AP.added(w),
      AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok)),
    tag_default(w, none))

# LAW: with no entry given, the entry is the checkout's
law entry_default:
  for +w: A.World
  for none: {A.entry.arg(w) == "" : String}
  {AP.entry(w) == Git.entry.maybe(K.look(AP.files(w), "ez.toml")) : String}

def entry_default(w, none):
  %Equal.sym(String, A.entry.arg(w), "", none) : {Bool.pick(String, String.is_empty(_),
    Git.entry.maybe(AP.tree.toml(w)), _) == Git.entry.maybe(K.look(AP.files(w), "ez.toml"))
    : String}
  {==}

def Laws.add_entry_default(w, none, ok):
  Equal.trans(String, M.dep.entry(AP.added(w)), AP.entry(w),
    Git.entry.maybe(K.look(AP.files(w), "ez.toml")),
    Equal.cong(M.Dep, String, d => M.dep.entry(d), AP.added(w),
      AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok)),
    entry_default(w, none))

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

def ws(k: K.Walked) -> List<&2, K.File>:
  match k:
    case K.Walked{_h, _r, _fs, ss}:
      ss
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# LAW: a walk that ends in success has the effects its package makes
law effects_is:
  for k: K.Walked
  for +w: A.World
  for s: {AP.outcome.k(k, w) == P.Success{} : P.Outcome}
  {AP.effects.k(k, w) == AP.effects.of(AP.dep.of(wh(k), wr(k), w), wh(k), AP.at.of(wr(k), w),
    wf(k), ws(k), A.manifest.of(A.read(w)), w) : List<&2, P.Effect>}

def effects_is(k, w, s):
  match k:
    case K.Walked{_h, _r, _fs, _ss}:
      {==}
    case K.Asks{at}:
      Eq.bit.absurd(&2, {AP.effects.k(K.Asks{at}, w) == AP.effects.of(AP.dep.of("", "", w),
        "", AP.at.of("", w), [], [], A.manifest.of(A.read(w)), w) : List<&2, P.Effect>},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Asks{at}, w)), False{},
            asks_loses(got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {AP.effects.k(K.Refused{why}, w) == AP.effects.of(AP.dep.of("", "", w),
        "", AP.at.of("", w), [], [], A.manifest.of(A.read(w)), w) : List<&2, P.Effect>},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Refused{why}, w)), False{},
            refused_loses(got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

# the parts of what an add writes after the ledger, named
def nxt(+d: M.Dep, +m: M.Manifest, +w: A.World) -> String:
  I.sync(A.deps.of(Rend.add.keep(m, d)), A.ignore(w))

def gss(+d: M.Dep, +h: String, +m: M.Manifest) -> List<&2, String>:
  AP.gone(M.find(A.deps.of(m), M.dep.name(d)), h, A.deps.of(Rend.add.keep(m, d)))

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
law drops_keep:
  for gs: List<&2, String>
  for rest: List<&2, P.Effect>
  for +p: String
  for e: {P.put.in(rest, p) == P.Kept{} : P.Wrote}
  {P.put.in(P.drops.of(gs, rest), p) == P.Kept{} : P.Wrote}

def drops_keep(gs, rest, p, e):
  match gs:
    case []:
      e
    case _h <> t:
      drops_keep(t, rest, p, e)

# LAW: so what follows the `.gitignore` write writes nothing
law tail_keep:
  for +h: String
  for +a: String
  for +w: A.World
  for gs: List<&2, String>
  for +p: String
  {P.put.in(P.drops.of(gs, AP.says(h, a, w)), p) == P.Kept{} : P.Wrote}

def tail_keep(h, a, w, gs, p):
  drops_keep(gs, AP.says(h, a, w), p,
    says_keep(String.is_empty(AP.tag(w)), Git.import.line(h, a),
      AP.tag(w) ++ " is " ++ AP.rev(w), p))

# LAW: and nothing after the ledger's write writes ez.toml
law ignore_keeps_ledger:
  for b: Bool
  for +next: String
  for gs: List<&2, String>
  for +h: String
  for +a: String
  for +w: A.World
  {P.put.in(AP.ignore.put(b, next, P.drops.of(gs, AP.says(h, a, w))), "ez.toml") == P.Kept{}
    : P.Wrote}

def ignore_keeps_ledger(b, next, gs, h, a, w):
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
  for ss: List<&2, K.File>
  for +m: M.Manifest
  for +w: A.World
  {P.put.in(AP.effects.of(d, h, a, fs, ss, m, w), "ez.toml")
    == P.Put{Rend.show(Rend.add.keep(m, d))} : P.Wrote}

def edits_of(d, h, a, _fs, _ss, m, w):
  write_then_keep(Rend.show(Rend.add.keep(m, d)),
    AP.ignore.put(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w),
      P.drops.of(gss(d, h, m), AP.says(h, a, w))),
    ignore_keeps_ledger(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w), gss(d, h, m),
      h, a, w))

# the dependency and the effects of the walk of an add, named
def dd(+w: A.World) -> M.Dep:
  AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w)

def aa(+w: A.World) -> String:
  AP.at.of(wr(AP.walked(w)), w)

def eff(+w: A.World) -> List<&2, P.Effect>:
  AP.effects.of(dd(w), wh(AP.walked(w)), aa(w), wf(AP.walked(w)), ws(AP.walked(w)),
    A.manifest.of(A.read(w)), w)

# the manifest of a ledger that read, as the premise gives it
def good_m(
  +w: A.World,
  +m: M.Manifest,
  good: {A.read(w) == M.Good{m} : M.Read}
) -> {A.manifest.of(A.read(w)) == m : M.Manifest}:
  Equal.cong(M.Read, M.Manifest, r => A.manifest.of(r), A.read(w), M.Good{m}, good)

def Laws.add_edits_ledger(w, m, good, ok):
  %Equal.sym(P.Plan, AP.plan(w), P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    succeeds(w, ok))
    : {P.put.plan(_, "ez.toml") == P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))} : P.Wrote}
  %Equal.sym(M.Dep, AP.added(w), dd(w), added_ok(w, ok))
    : {P.put.in(AP.effects.k(AP.walked(w), w), "ez.toml") == P.Put{Rend.show(Rend.add.keep(m,
      _))} : P.Wrote}
  %Equal.sym(List<&2, P.Effect>, AP.effects.k(AP.walked(w), w), eff(w),
    effects_is(AP.walked(w), w, won(w, ok)))
    : {P.put.in(_, "ez.toml") == P.Put{Rend.show(Rend.add.keep(m, dd(w)))} : P.Wrote}
  %good_m(w, m, good)
    : {P.put.in(eff(w), "ez.toml") == P.Put{Rend.show(Rend.add.keep(_, dd(w)))} : P.Wrote}
  edits_of(dd(w), wh(AP.walked(w)), aa(w), wf(AP.walked(w)), ws(AP.walked(w)),
    A.manifest.of(A.read(w)), w)

# LAW: what `.gitignore` holds after the effects: the text `I.sync` gave,
# whether it was written or, being the same text, kept
law syncs_arm:
  for b: Bool
  for +next: String
  for +ig: String
  for +text: String
  for gs: List<&2, String>
  for +h: String
  for +a: String
  for +w: A.World
  for eb: {String.eq(next, ig) == b : Bool}
  {AP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore",
    P.put.in(AP.ignore.put(b, next, P.drops.of(gs, AP.says(h, a, w))), ".gitignore")), ig)
    == next : String}

def syncs_arm(b, next, ig, text, gs, h, a, w, eb):
  match b:
    case True{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(gs, AP.says(h, a, w)), ".gitignore"), P.Kept{},
        tail_keep(h, a, w, gs, ".gitignore"))
        : {AP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore", _), ig) == next : String}
      Equal.sym(String, next, ig, Str.string_eq_true(next, ig, eb))
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(gs, AP.says(h, a, w)), ".gitignore"), P.Kept{},
        tail_keep(h, a, w, gs, ".gitignore"))
        : {AP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore",
          P.put.one(P.Write{".gitignore", next}, ".gitignore", _)), ig) == next : String}
      {==}

# LAW: the effects of a package leave `.gitignore` holding `I.sync` over the
# edited ledger
law syncs_of:
  for +d: M.Dep
  for +h: String
  for +a: String
  for fs: List<&2, K.Source>
  for ss: List<&2, K.File>
  for +m: M.Manifest
  for +w: A.World
  {AP.after(P.put.in(AP.effects.of(d, h, a, fs, ss, m, w), ".gitignore"), A.ignore(w))
    == nxt(d, m, w) : String}

def syncs_of(d, h, a, _fs, _ss, m, w):
  syncs_arm(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w), A.ignore(w),
    Rend.show(Rend.add.keep(m, d)), gss(d, h, m), h, a, w, {==})

def Laws.add_syncs_allowlist(w, m, good, ok):
  %Equal.sym(P.Plan, AP.plan(w), P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    succeeds(w, ok))
    : {AP.after(P.put.plan(_, ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(m, AP.added(w))), A.ignore(w)) : String}
  %Equal.sym(M.Dep, AP.added(w), dd(w), added_ok(w, ok))
    : {AP.after(P.put.in(AP.effects.k(AP.walked(w), w), ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(m, _)), A.ignore(w)) : String}
  %Equal.sym(List<&2, P.Effect>, AP.effects.k(AP.walked(w), w), eff(w),
    effects_is(AP.walked(w), w, won(w, ok)))
    : {AP.after(P.put.in(_, ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(m, dd(w))), A.ignore(w)) : String}
  %good_m(w, m, good)
    : {AP.after(P.put.in(eff(w), ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(_, dd(w))), A.ignore(w)) : String}
  syncs_of(dd(w), wh(AP.walked(w)), aa(w), wf(AP.walked(w)), ws(AP.walked(w)),
    A.manifest.of(A.read(w)), w)

# ---------------------------------------------------------------------------
# what an add says

# LAW: the lines a person is told end with the import line
law says_last:
  for c: Bool
  for +a: String
  for +b: String
  {AP.last.go(P.said.in(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{b}, P.Say{a}])),
    "") == a : String}

def says_last(c, _a, _b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the committed trees removed ahead of them say nothing
law drops_said:
  for gs: List<&2, String>
  for rest: List<&2, P.Effect>
  {P.said.in(P.drops.of(gs, rest)) == P.said.in(rest) : List<&2, String>}

def drops_said(gs, rest):
  match gs:
    case []:
      {==}
    case _h <> t:
      drops_said(t, rest)

# LAW: nor does the `.gitignore` write, whether or not it is made
law ignore_said:
  for b: Bool
  for +next: String
  for rest: List<&2, P.Effect>
  {P.said.in(AP.ignore.put(b, next, rest)) == P.said.in(rest) : List<&2, String>}

def ignore_said(b, _next, _rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the effects of a package end what they say with the import line for
# the entry at `a` inside it
law says_of:
  for +d: M.Dep
  for +h: String
  for +a: String
  for fs: List<&2, K.Source>
  for ss: List<&2, K.File>
  for +m: M.Manifest
  for +w: A.World
  {AP.last.go(P.said.in(AP.effects.of(d, h, a, fs, ss, m, w)), "") == Git.import.line(h, a)
    : String}

def says_of(d, h, a, _fs, _ss, m, w):
  %Equal.sym(List<&2, String>,
    P.said.in(AP.ignore.put(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w),
      P.drops.of(gss(d, h, m), AP.says(h, a, w)))),
    P.said.in(P.drops.of(gss(d, h, m), AP.says(h, a, w))),
    ignore_said(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w),
      P.drops.of(gss(d, h, m), AP.says(h, a, w))))
    : {AP.last.go(_, "") == Git.import.line(h, a) : String}
  %Equal.sym(List<&2, String>, P.said.in(P.drops.of(gss(d, h, m), AP.says(h, a, w))),
    P.said.in(AP.says(h, a, w)), drops_said(gss(d, h, m), AP.says(h, a, w)))
    : {AP.last.go(_, "") == Git.import.line(h, a) : String}
  says_last(String.is_empty(AP.tag(w)), Git.import.line(h, a),
    AP.tag(w) ++ " is " ++ AP.rev(w))

# LAW: a walk that ends in success ends what the add says with the import
# line for its package's entry
law says_k:
  for k: K.Walked
  for +w: A.World
  for s: {AP.outcome.k(k, w) == P.Success{} : P.Outcome}
  {AP.last.go(P.said.in(AP.effects.k(k, w)), "")
    == Git.import.line(AP.hash.of(k), AP.at.of(AP.root.of(k), w)) : String}

def says_k(k, w, s):
  match k:
    case K.Walked{+h, +r, fs, ss}:
      says_of(AP.dep.of(h, r, w), h, AP.at.of(r, w), fs, ss, A.manifest.of(A.read(w)), w)
    case K.Asks{at}:
      Eq.bit.absurd(&2, {AP.last.go(P.said.in(AP.effects.k(K.Asks{at}, w)), "")
        == Git.import.line("", AP.at.of(".", w)) : String},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Asks{at}, w)), False{},
            asks_loses(got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {AP.last.go(P.said.in(AP.effects.k(K.Refused{why}, w)), "")
        == Git.import.line("", AP.at.of(".", w)) : String},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Refused{why}, w)), False{},
            refused_loses(got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

def Laws.add_says_import(w, ok):
  %Equal.sym(P.Plan, AP.plan(w), P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    succeeds(w, ok))
    : {AP.last(_) == Git.import.line(AP.hash(w), AP.at(w)) : String}
  says_k(AP.walked(w), w, won(w, ok))

# ---------------------------------------------------------------------------
# refusals after the walk

# LAW: an outcome that is no success seals a plan that refuses
law seal_refused:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {win(o) == False{} : Bool}
  {AP.refuses.plan(AP.seal(es, o)) == True{} : Bool}

def seal_refused(es, o, e):
  match o:
    case P.Success{}:
      Eq.bit.absurd2(&2, {AP.refuses.plan(AP.seal(es, P.Success{})) == True{} : Bool}, e)
    case P.Refused{_why}:
      {==}

# LAW: an add whose walk ends in no success refuses, whatever the verdict
law lose_v:
  for v: AP.Verdict
  for +w: A.World
  for e: {win(AP.outcome.k(AP.walked(w), w)) == False{} : Bool}
  {AP.refuses.plan(AP.plan.v(v, w)) == True{} : Bool}

def lose_v(v, w, e):
  match v:
    case AP.Go{}:
      seal_refused(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), e)
    case AP.Wait{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

# The lookup is rewritten to the None the premise gives, which is refused.
def entry_loses(
  +w: A.World,
  miss: {None{} == got(w) : Maybe<&2, String>}
) -> {win(AP.outcome.k(AP.walked(w), w)) == False{} : Bool}:
  %miss : {win(AP.outcome.entry(_, AP.walked(w), w)) == False{} : Bool}
  {==}

def Laws.add_entry_absent(w, miss):
  lose_v(AP.decide(w), w, entry_loses(w, miss))

law named_walk:
  for k: K.Walked
  for +w: A.World
  for e: {False{} == String.is_empty(AP.why(w)) : Bool}
  {win(AP.outcome.walk(k, w)) == False{} : Bool}

def named_walk(k, w, e):
  match k:
    case K.Walked{+h, +r, _fs, _ss}:
      %e : {win(AP.outcome.name(_,
        Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.dep.of(h, r, w))), w))
        == False{} : Bool}
      {==}
    case K.Asks{_at}:
      {==}
    case K.Refused{_why}:
      {==}

# LAW: a name `Named.why.as` objects to loses, whatever the entry lookup and
# the walk
law named_loses:
  for g: Maybe<&2, String>
  for k: K.Walked
  for +w: A.World
  for e: {False{} == String.is_empty(AP.why(w)) : Bool}
  {win(AP.outcome.entry(g, k, w)) == False{} : Bool}

def named_loses(g, k, w, e):
  match g:
    case None{}:
      {==}
    case Some{_t}:
      named_walk(k, w, e)

def Laws.add_refuses_named(w, why):
  lose_v(AP.decide(w), w, named_loses(got(w), AP.walked(w), w, why))

# LAW: a walk that refuses loses, whatever the entry lookup
law walk_loses:
  for g: Maybe<&2, String>
  for +w: A.World
  for +why: String
  for e: {AP.walked(w) == K.Refused{why} : K.Walked}
  {win(AP.outcome.entry(g, AP.walked(w), w)) == False{} : Bool}

def walk_loses(g, w, why, e):
  match g:
    case None{}:
      {==}
    case Some{_t}:
      %Equal.sym(K.Walked, AP.walked(w), K.Refused{why}, e)
        : {win(AP.outcome.walk(_, w)) == False{} : Bool}
      {==}

def Laws.add_walk_refused(w, why, e):
  lose_v(AP.decide(w), w, walk_loses(got(w), w, why, e))

# ---------------------------------------------------------------------------
# the questions

# LAW: a question about a source names that source
law url_of_ask:
  for q: AP.Q
  for +f: String
  {AP.ask.url(AP.ask.of(q, f)) == f : String}

def url_of_ask(q, _f):
  match q:
    case AP.QTags{}:
      {==}
    case AP.QHead{}:
      {==}
    case AP.QRefs{_ref}:
      {==}
    case AP.QClone{_rev}:
      {==}

# LAW: so every question about a source names it
law from_all:
  for qs: List<&2, AP.Q>
  for +f: String
  {AP.asks.from(AP.asks.of(qs, f), f) == True{} : Bool}

def from_all(qs, f):
  match qs:
    case []:
      {==}
    case h <> t:
      %Equal.sym(Bool, AP.asks.from(AP.asks.of(t, f), f), True{}, from_all(t, f))
        : {Bool.and(String.eq(AP.ask.url(AP.ask.of(h, f)), f), _) == True{} : Bool}
      %Equal.sym(String, AP.ask.url(AP.ask.of(h, f)), f, url_of_ask(h, f))
        : {Bool.and(String.eq(_, f), True{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(f, f), True{}, Eq.string_eq_self(f))
        : {Bool.and(_, True{}) == True{} : Bool}
      {==}

def Laws.add_asks_anchored(w):
  from_all(AP.qs.v(AP.decide(w)), A.from(w))

# LAW: the checkout is no question about a ref
law co_resolves:
  for c: AP.Co
  for +rev: String
  for +f: String
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.co(c, rev)), f)) == False{} : Bool}

def co_resolves(c, _rev, _f):
  match c:
    case AP.Co{_nar, _fs}:
      {==}
    case AP.CoWait{}:
      {==}
    case AP.CoNo{_why}:
      {==}

# LAW: past the early refusals, a 40-hex ref asks only for the checkout
law early_resolves:
  for b: Bool
  for +why: String
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.early(b, why, w)), A.from(w))) == False{} : Bool}

def early_resolves(b, _why, w, hex):
  match b:
    case True{}:
      %Equal.sym(Bool, Git.is_rev(A.ref(w)), True{}, hex)
        : {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.tip(AP.tip.of(_,
          String.is_empty(A.ref(w)), w), w)), A.from(w))) == False{} : Bool}
      co_resolves(AP.co.at(w, A.ref(w)), A.ref(w), A.from(w))
    case False{}:
      {==}

law place_resolves:
  for p: Tgt.Place
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.place(p, w)), A.from(w))) == False{} : Bool}

def place_resolves(p, w, hex):
  match p:
    case Tgt.Bad{_why}:
      {==}
    case Tgt.Local{_path}:
      early_resolves(String.is_empty(AP.early(w)), AP.early(w), w, hex)
    case Tgt.Remote{_url, _slug}:
      early_resolves(String.is_empty(AP.early(w)), AP.early(w), w, hex)

law read_resolves:
  for r: M.Read
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.read(r, w)), A.from(w))) == False{} : Bool}

def read_resolves(r, w, hex):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      place_resolves(A.place(w), w, hex)

def Laws.add_commit_asks_nothing(w, hex):
  read_resolves(A.read(w), w, hex)

# ---------------------------------------------------------------------------
# the tree laid

# a walk's package with its hash and file list made again from its texts
def fix(k: K.Walked) -> K.Walked:
  match k:
    case K.Walked{_h, +r, +fs, _ss}:
      K.Walked{K.hash_of(K.files_of(K.laid.sums(fs))), r, fs, K.files_of(K.laid.sums(fs))}
    case K.Asks{at}:
      K.Asks{at}
    case K.Refused{why}:
      K.Refused{why}

# LAW: a package the walk judged is its texts' own: the found files placed
# and weighed are the laid ones weighed (`Pk.placed_is_laid`)
law fixed_judge:
  for ok: Bool
  for +bad: String
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {fix(K.made.judge(ok, bad, root, pre, K.files_of(K.placed(pre, K.hit.sums(out))), out))
    == K.made.judge(ok, bad, root, pre, K.files_of(K.placed(pre, K.hit.sums(out))), out)
    : K.Walked}

def fixed_judge(ok, _bad, root, pre, out):
  match ok:
    case True{}:
      %Equal.sym(List<&2, K.File>, K.placed(pre, K.hit.sums(out)),
        K.laid.sums(K.laid(pre, out)), Pk.placed_is_laid(pre, out))
        : {K.Walked{K.hash_of(K.files_of(K.laid.sums(K.laid(pre, out)))), root, K.laid(pre, out),
          K.files_of(K.laid.sums(K.laid(pre, out)))}
          == K.Walked{K.hash_of(K.files_of(_)), root, K.laid(pre, out), K.files_of(_)}
          : K.Walked}
      {==}
    case False{}:
      {==}

law fixed_placed:
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {fix(K.made.placed(root, pre, out)) == K.made.placed(root, pre, out) : K.Walked}

def fixed_placed(root, pre, out):
  fixed_judge(String.is_empty(K.escaped(K.files_of(K.placed(pre, K.hit.sums(out))))),
    K.escaped(K.files_of(K.placed(pre, K.hit.sums(out)))), root, pre, out)

# LAW: a package the license check judged is its texts' own too: a refusal
# names no texts, and a pass is the placed package
law fixed_lic:
  for ok: Bool
  for +bad: String
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {fix(K.made.lic(ok, bad, root, pre, out)) == K.made.lic(ok, bad, root, pre, out) : K.Walked}

def fixed_lic(ok, _bad, root, pre, out):
  match ok:
    case True{}:
      fixed_placed(root, pre, out)
    case False{}:
      {==}

law fixed_checked:
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {fix(K.made.checked(root, pre, out)) == K.made.checked(root, pre, out) : K.Walked}

def fixed_checked(root, pre, out):
  fixed_lic(String.is_empty(K.licensed(pre, out)), K.licensed(pre, out), root, pre, out)

law fixed_anc:
  for far: Bool
  for +levels: Nat
  for +dir: String
  for +out: List<&2, K.Hit>
  {fix(K.made.anc(far, levels, dir, out)) == K.made.anc(far, levels, dir, out) : K.Walked}

def fixed_anc(far, levels, dir, out):
  match far:
    case True{}:
      {==}
    case False{}:
      fixed_checked(Path.climb(levels, dir), Path.tail(dir, levels), out)

law fixed_climb:
  for levels: Nat
  for +dir: String
  for +out: List<&2, K.Hit>
  {fix(K.made.climb(levels, dir, out)) == K.made.climb(levels, dir, out) : K.Walked}

def fixed_climb(levels, dir, out):
  match levels:
    case 0n:
      fixed_checked(Path.norm(dir), "", out)
    case 1n+ +p:
      fixed_anc(Nat.is_gt((1n + p : Nat), K.comps(dir)), (1n + p : Nat), dir, out)

law fixed_go:
  for stop: K.Stop
  for +entry: String
  for +out: List<&2, K.Hit>
  {fix(K.made.go(stop, entry, out)) == K.made.go(stop, entry, out) : K.Walked}

def fixed_go(stop, entry, out):
  match stop:
    case K.Going{}:
      fixed_climb(K.climb(out), Path.dir(entry), out)
    case K.Missing{_at}:
      {==}
    case K.Climbs{_at}:
      {==}
    case K.Asking{_at}:
      {==}
    case K.Spent{}:
      {==}

law fixed_made:
  for +entry: String
  for st: K.State
  {fix(K.made(entry, st)) == K.made(entry, st) : K.Walked}

def fixed_made(entry, st):
  match st:
    case K.State{_seen, out, stop, _queue}:
      fixed_go(stop, entry, out)

# LAW: the walk of an add is its texts' own
law fixed_walked:
  for +w: A.World
  {fix(AP.walked(w)) == AP.walked(w) : K.Walked}

def fixed_walked(w):
  fixed_made(Path.norm(AP.entry(w)), K.walk(AP.fuel(AP.files(w)),
    K.Tree{True{}, AP.files(w), []}, Path.base(Path.norm(AP.entry(w))),
    K.start(Path.norm(AP.entry(w)))))

# LAW: all but the last of a list with one more at its end is the list
law front_snoc:
  for xs: List<&2, W.Source>
  for x: W.Source
  {P.front(List.append(&2, W.Source, xs, [x])) == xs : List<&2, W.Source>}

def front_snoc(xs, x):
  match xs:
    case []:
      {==}
    case h <> t:
      match t:
        case []:
          {==}
        case h2 <> t2:
          Equal.cong(List<&2, W.Source>, List<&2, W.Source>, ys => h <> ys,
            P.front(List.append(&2, W.Source, h2 <> t2, [x])), h2 <> t2,
            front_snoc(h2 <> t2, x))

# LAW: and the last one's text is its text
law last_snoc:
  for xs: List<&2, W.Source>
  for at: String
  for text: String
  {P.last(List.append(&2, W.Source, xs, [W.Source{at, text}])) == text : String}

def last_snoc(xs, at, text):
  match xs:
    case []:
      {==}
    case _h <> t:
      match t:
        case []:
          {==}
        case h2 <> t2:
          last_snoc(h2 <> t2, at, text)

# LAW: the found files as laid, weighed, are the walk's laid files weighed
law weigh_srcs:
  for fs: List<&2, K.Source>
  {W.weighs(AP.srcs(fs)) == K.laid.sums(fs) : List<&2, K.File>}

def weigh_srcs(fs):
  match fs:
    case []:
      {==}
    case K.Source{at, text} <> t:
      Equal.cong(List<&2, K.File>, List<&2, K.File>, ys => K.File{at, Sha.hex(text)} <> ys,
        W.weighs(AP.srcs(t)), K.laid.sums(t), weigh_srcs(t))

# a package's file list, weighed from its texts, and the files a `Lay`
# writes for it
def lsum(fs: List<&2, K.Source>) -> List<&2, K.File>:
  K.files_of(K.laid.sums(fs))

def lh(fs: List<&2, K.Source>) -> String:
  K.hash_of(lsum(fs))

def lay.files(+fs: List<&2, K.Source>) -> List<&2, W.Source>:
  List.append(&2, W.Source, AP.srcs(fs), [W.Source{"manifest", K.manifest_of(lsum(fs))}])

# LAW: a tree laid from a package's texts, with its manifest last and named
# by its hash, is named
law lay_canon:
  for +fs: List<&2, K.Source>
  {P.lay.named(lh(fs), lay.files(fs)) == True{} : Bool}

def lay_canon(fs):
  %Equal.sym(List<&2, W.Source>, P.front(lay.files(fs)), AP.srcs(fs),
    front_snoc(AP.srcs(fs), W.Source{"manifest", K.manifest_of(lsum(fs))}))
    : {Bool.and(String.eq(lh(fs), K.hash_of(K.files_of(W.weighs(_)))),
      String.eq(P.last(lay.files(fs)), K.manifest_of(K.files_of(W.weighs(_))))) == True{}
      : Bool}
  %Equal.sym(List<&2, K.File>, W.weighs(AP.srcs(fs)), K.laid.sums(fs), weigh_srcs(fs))
    : {Bool.and(String.eq(lh(fs), K.hash_of(K.files_of(_))),
      String.eq(P.last(lay.files(fs)), K.manifest_of(K.files_of(_)))) == True{} : Bool}
  %Equal.sym(String, P.last(lay.files(fs)), K.manifest_of(lsum(fs)),
    last_snoc(AP.srcs(fs), "manifest", K.manifest_of(lsum(fs))))
    : {Bool.and(String.eq(lh(fs), lh(fs)), String.eq(_, K.manifest_of(lsum(fs)))) == True{}
      : Bool}
  %Equal.sym(Bool, String.eq(lh(fs), lh(fs)), True{}, Eq.string_eq_self(lh(fs)))
    : {Bool.and(_, String.eq(K.manifest_of(lsum(fs)), K.manifest_of(lsum(fs)))) == True{}
      : Bool}
  Eq.string_eq_self(K.manifest_of(lsum(fs)))

# LAW: the lines a person is told lay nothing
law says_lays:
  for c: Bool
  for +a: String
  for +b: String
  {P.lays.named(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{b}, P.Say{a}]))
    == True{} : Bool}

def says_lays(c, _a, _b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law drops_lays:
  for gs: List<&2, String>
  for rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.drops.of(gs, rest)) == True{} : Bool}

def drops_lays(gs, rest, e):
  match gs:
    case []:
      e
    case _h <> t:
      drops_lays(t, rest, e)

law ignore_lays:
  for b: Bool
  for +next: String
  for gs: List<&2, String>
  for +h: String
  for +a: String
  for +w: A.World
  {P.lays.named(AP.ignore.put(b, next, P.drops.of(gs, AP.says(h, a, w)))) == True{} : Bool}

def ignore_lays(b, _next, gs, h, a, w):
  match b:
    case True{}:
      drops_lays(gs, AP.says(h, a, w), says_lays(String.is_empty(AP.tag(w)),
        Git.import.line(h, a), AP.tag(w) ++ " is " ++ AP.rev(w)))
    case False{}:
      drops_lays(gs, AP.says(h, a, w), says_lays(String.is_empty(AP.tag(w)),
        Git.import.line(h, a), AP.tag(w) ++ " is " ++ AP.rev(w)))

# LAW: both halves of an `and` that are True
law both:
  for x: Bool
  for y: Bool
  for ex: {x == True{} : Bool}
  for ey: {y == True{} : Bool}
  {Bool.and(x, y) == True{} : Bool}

def both(x, y, ex, ey):
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

# LAW: the effects of a package made again from its texts lay a named tree
law lays_of:
  for +d: M.Dep
  for +a: String
  for +fs: List<&2, K.Source>
  for +m: M.Manifest
  for +w: A.World
  {P.lays.named(AP.effects.of(d, lh(fs), a, fs, lsum(fs), m, w)) == True{} : Bool}

def lays_of(d, a, fs, m, w):
  both(P.lay.named(lh(fs), lay.files(fs)),
    P.lays.named(AP.ignore.put(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w),
      P.drops.of(gss(d, lh(fs), m), AP.says(lh(fs), a, w)))),
    lay_canon(fs),
    ignore_lays(String.eq(nxt(d, m, w), A.ignore(w)), nxt(d, m, w), gss(d, lh(fs), m),
      lh(fs), a, w))

law lays_fixed:
  for k: K.Walked
  for +w: A.World
  {P.lays.named(AP.effects.k(fix(k), w)) == True{} : Bool}

def lays_fixed(k, w):
  match k:
    case K.Walked{_h, +r, +fs, _ss}:
      lays_of(AP.dep.of(lh(fs), r, w), AP.at.of(r, w), fs, A.manifest.of(A.read(w)), w)
    case K.Asks{_at}:
      {==}
    case K.Refused{_why}:
      {==}

law lays_walked:
  for +w: A.World
  {P.lays.named(AP.effects.k(AP.walked(w), w)) == True{} : Bool}

def lays_walked(w):
  %fixed_walked(w) : {P.lays.named(AP.effects.k(_, w)) == True{} : Bool}
  lays_fixed(AP.walked(w), w)

law lays_seal:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {P.lays.named(es) == True{} : Bool}
  {P.lays.named(P.effects(AP.seal(es, o))) == True{} : Bool}

def lays_seal(_es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

law lays_v:
  for v: AP.Verdict
  for +w: A.World
  {P.lays.named(P.effects(AP.plan.v(v, w))) == True{} : Bool}

def lays_v(v, w):
  match v:
    case AP.Go{}:
      lays_seal(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), lays_walked(w))
    case AP.Wait{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

def Laws.add_lays_named(w):
  lays_v(AP.decide(w), w)

# ---------------------------------------------------------------------------
# the commit pinned

# LAW: the commit a found rev gives is that rev, "" giving none
law found_rev:
  for +e: String
  for why: String
  {AP.tip.rev(AP.tip.found(e, why)) == e : String}

def found_rev(e, _why):
  match e:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# LAW: a named ref's commit is what `Git.exact` reads from what was printed
law named_rev:
  for s: Up.Said
  for +w: A.World
  {AP.tip.rev(AP.tip.refs(s, w))
    == Git.exact(Git.rows(String.lines(AP.said.text(s))), A.ref(w)) : String}

def named_rev(s, w):
  match s:
    case Up.Said{+text}:
      found_rev(Git.exact(Git.rows(String.lines(text)), A.ref(w)),
        "ez: " ++ A.url(w) ++ " has no ref named " ++ A.ref(w))
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law rev_named:
  for +w: A.World
  for nr: {Git.is_rev(A.ref(w)) == False{} : Bool}
  for ne: {String.is_empty(A.ref(w)) == False{} : Bool}
  {AP.rev(w) == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}

def rev_named(w, nr, ne):
  %Equal.sym(Bool, Git.is_rev(A.ref(w)), False{}, nr)
    : {AP.tip.rev(AP.tip.of(_, String.is_empty(A.ref(w)), w))
      == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}
  %Equal.sym(Bool, String.is_empty(A.ref(w)), False{}, ne)
    : {AP.tip.rev(AP.tip.of(False{}, _, w))
      == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}
  named_rev(AP.said(w, AP.QRefs{A.ref(w)}), w)

def Laws.add_pins_named(w, nr, ne, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w),
    Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok)),
    rev_named(w, nr, ne))

# LAW: the chosen tag's commit, when a tag was chosen
law chosen_rev:
  for s: Up.Said
  for +w: A.World
  for c: {String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(s))))))
    == False{} : Bool}
  {AP.tip.rev(AP.tip.tags(s, w)) == Git.exact(Git.rows(String.lines(AP.said.text(s))),
    Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(s)))))) : String}

def chosen_rev(s, w, c):
  match s:
    case Up.Said{+text}:
      %Equal.sym(Bool, String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))),
        False{}, c)
        : {AP.tip.rev(AP.tip.chosen(_, Git.choose(Git.tag.names(Git.rows(String.lines(text)))),
          Git.rows(String.lines(text)), w)) == Git.exact(Git.rows(String.lines(text)),
          Git.choose(Git.tag.names(Git.rows(String.lines(text))))) : String}
      found_rev(Git.exact(Git.rows(String.lines(text)),
        Git.choose(Git.tag.names(Git.rows(String.lines(text))))),
        "ez: " ++ A.url(w) ++ " has no tag named " ++
          Git.choose(Git.tag.names(Git.rows(String.lines(text)))))
    case Up.Unsaid{why}:
      Eq.bit.absurd2(&2, {AP.tip.rev(AP.tip.tags(Up.Unsaid{why}, w))
        == Git.exact(Git.rows(String.lines(AP.said.text(Up.Unsaid{why}))),
          Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(Up.Unsaid{why}))))))
        : String}, c)
    case Up.Unasked{ask}:
      Eq.bit.absurd2(&2, {AP.tip.rev(AP.tip.tags(Up.Unasked{ask}, w))
        == Git.exact(Git.rows(String.lines(AP.said.text(Up.Unasked{ask}))),
          Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(Up.Unasked{ask}))))))
        : String}, c)

law rev_chosen:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for c: {String.is_empty(Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))) == False{}
    : Bool}
  {AP.rev(w) == Git.exact(AP.rows(w, AP.QTags{}),
    Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))) : String}

def rev_chosen(w, none, c):
  %Equal.sym(String, A.ref(w), "", none)
    : {AP.tip.rev(AP.tip.of(Git.is_rev(_), String.is_empty(_), w))
      == Git.exact(AP.rows(w, AP.QTags{}), Git.choose(Git.tag.names(AP.rows(w, AP.QTags{}))))
      : String}
  chosen_rev(AP.said(w, AP.QTags{}), w, c)

def Laws.add_pins_chosen_rev(w, none, c, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w),
    Git.exact(AP.rows(w, AP.QTags{}), Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok)),
    rev_chosen(w, none, c))

law rev_commit:
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.rev(w) == A.ref(w) : String}

def rev_commit(w, hex):
  %Equal.sym(Bool, Git.is_rev(A.ref(w)), True{}, hex)
    : {AP.tip.rev(AP.tip.of(_, String.is_empty(A.ref(w)), w)) == A.ref(w) : String}
  {==}

def Laws.add_pins_commit(w, hex, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w), A.ref(w),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok)),
    rev_commit(w, hex))

# LAW: HEAD's commit, when its symref names a branch
law head_rev:
  for s: Up.Said
  for +w: A.World
  for b: {String.is_empty(Git.tip.branch(Git.rows(String.lines(AP.said.text(s))))) == False{}
    : Bool}
  {AP.tip.rev(AP.tip.head(s, w)) == Git.tip.rev(Git.rows(String.lines(AP.said.text(s))))
    : String}

def head_rev(s, w, b):
  match s:
    case Up.Said{+text}:
      %Equal.sym(Bool, String.is_empty(Git.tip.branch(Git.rows(String.lines(text)))), False{}, b)
        : {AP.tip.rev(Bool.pick(AP.Tip, _,
          AP.TipNo{"ez: " ++ A.url(w) ++
            " has no semver-ish tag and its HEAD names no branch; name a ref to pin"},
          AP.tip.found(Git.tip.rev(Git.rows(String.lines(text))),
            "ez: " ++ A.url(w) ++ " has no HEAD")))
          == Git.tip.rev(Git.rows(String.lines(text))) : String}
      found_rev(Git.tip.rev(Git.rows(String.lines(text))), "ez: " ++ A.url(w) ++ " has no HEAD")
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law rev_head:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for +text: String
  for t: {AP.said(w, AP.QTags{}) == Up.Said{text} : Up.Said}
  for c: {String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))) == True{}
    : Bool}
  for b: {String.is_empty(Git.tip.branch(AP.rows(w, AP.QHead{}))) == False{} : Bool}
  {AP.rev(w) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}

def rev_head(w, none, text, t, c, b):
  %Equal.sym(String, A.ref(w), "", none)
    : {AP.tip.rev(AP.tip.of(Git.is_rev(_), String.is_empty(_), w))
      == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}
  %Equal.sym(Up.Said, AP.said(w, AP.QTags{}), Up.Said{text}, t)
    : {AP.tip.rev(AP.tip.tags(_, w)) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}
  %Equal.sym(Bool, String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))),
    True{}, c)
    : {AP.tip.rev(AP.tip.chosen(_, Git.choose(Git.tag.names(Git.rows(String.lines(text)))),
      Git.rows(String.lines(text)), w)) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}
  head_rev(AP.said(w, AP.QHead{}), w, b)

def Laws.add_pins_head_rev(w, none, text, t, c, b, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w),
    Git.tip.rev(AP.rows(w, AP.QHead{})),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(wh(AP.walked(w)), wr(AP.walked(w)), w), added_ok(w, ok)),
    rev_head(w, none, text, t, c, b))

# EZ-LED-5: `Rend.add.keep` edits the dependencies and hands the tools on as
# they are, so the ledger `add_edits_ledger` names is this one.
def Laws.add_keeps_tools(w, n, e, b, h, ds, ts, good, ok):
  Laws.add_edits_ledger(w, M.Manifest{n, e, b, h, ds, ts}, good, ok)

# ---------------------------------------------------------------------------
# EZ-OUT-1

# LAW: a plan ends with the status of whether it refuses
law plan_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(AP.refuses.plan(pl)) : U32}

def plan_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.add_exits_as_it_refuses(w):
  plan_code(AP.plan(w))

# ---------------------------------------------------------------------------
# EZ-LED-4

# LAW: a package's outcome that is a success found the ledger it leaves
# renderable
law name_fit:
  for b: Bool
  for f: Bool
  for +w: A.World
  for s: {win(AP.outcome.name(b, f, w)) == True{} : Bool}
  {f == True{} : Bool}

def name_fit(b, f, w, s):
  match b f:
    case True{} True{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, s)
    case False{} _:
      Eq.bit.absurd(&2, {f == True{} : Bool}, s)

# LAW: so is a walk's outcome that is a success, with the entry lookup given
law entry_fit:
  for g: Maybe<&2, String>
  for +h: String
  for +r: String
  for fs: List<&2, K.Source>
  for ss: List<&2, K.File>
  for +w: A.World
  for s: {win(AP.outcome.entry(g, K.Walked{h, r, fs, ss}, w)) == True{} : Bool}
  {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.dep.of(h, r, w))) == True{} : Bool}

def entry_fit(g, h, r, fs, ss, w, s):
  match g:
    case None{}:
      Eq.bit.absurd(&2, {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.dep.of(h, r, w)))
        == True{} : Bool}, s)
    case Some{_t}:
      name_fit(String.is_empty(AP.why(w)),
        Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.dep.of(h, r, w))), w, s)

# LAW: an add whose walk ends in success leaves a renderable ledger
law fit_k:
  for k: K.Walked
  for +w: A.World
  for s: {AP.outcome.k(k, w) == P.Success{} : P.Outcome}
  {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.added.k(k, w))) == True{} : Bool}

def fit_k(k, w, s):
  match k:
    case K.Walked{+h, +r, fs, ss}:
      entry_fit(got(w), h, r, fs, ss, w,
        Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Walked{h, r, fs, ss}, w),
          P.Success{}, s))
    case K.Asks{at}:
      Eq.bit.absurd(&2, {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)),
        AP.added.k(K.Asks{at}, w))) == True{} : Bool},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Asks{at}, w)), False{},
            asks_loses(got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)),
        AP.added.k(K.Refused{why}, w))) == True{} : Bool},
        Equal.trans(Bool, False{}, win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, win(AP.outcome.k(K.Refused{why}, w)), False{},
            refused_loses(got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

# what a path was written with. Proof vocabulary.
def wrote.text(x: P.Wrote) -> String:
  match x:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# An add that does not refuse writes `Rend.add.keep`'s ledger
# (`add_edits_ledger`), whose walk ended in success, so the ledger is
# renderable and the manifest's round trip reads it back.
def Laws.add_ledger_reads_back(w, m, good, ok, text, put):
  +fit = Equal.trans(Bool, Rend.renderable(Rend.add.keep(m, AP.added(w))),
    Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.added(w))), True{},
    Equal.cong(M.Manifest, Bool, x => Rend.renderable(Rend.add.keep(x, AP.added(w))),
      m, A.manifest.of(A.read(w)),
      Equal.sym(M.Manifest, A.manifest.of(A.read(w)), m, good_m(w, m, good))),
    fit_k(AP.walked(w), w, won(w, ok)))
  +p = Equal.trans(P.Wrote, P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))},
    P.put.plan(AP.plan(w), "ez.toml"), P.Put{text},
    Equal.sym(P.Wrote, P.put.plan(AP.plan(w), "ez.toml"),
      P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))}, Laws.add_edits_ledger(w, m, good, ok)),
    put)
  +t = Equal.cong(P.Wrote, String, x => wrote.text(x),
    P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))}, P.Put{text}, p)
  %t : {M.parse(_) == M.Good{Rend.add.keep(m, AP.added(w))} : M.Read}
  ML.ledger_reads_back(Rend.add.keep(m, AP.added(w)), fit)
