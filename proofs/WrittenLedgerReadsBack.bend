# proofs of laws/WrittenLedgerReadsBack.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/pub/blurb.bend as B
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/init/plan.bend as IP
import ../src/remove/plan.bend as RP
import ../laws/AddDependencyIdempotent.bend as L1
import ../laws/RemoveDependencyIdempotent.bend as L2
import ../laws/WrittenLedgerReadsBack.bend as Laws
import ../laws/defs/LedgerReadsBackPremise.bend as D1
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2
import ./lemmas/PlanEffectFacts.bend as M3

# ---------------------------------------------------------------------------
# laws/WrittenLedgerReadsBack.bend

# LAW: a package's outcome that is a success found the ledger it leaves
# renderable
law name_fit:
  for b: Bool
  for f: Bool
  for +w: A.World
  for s: {M2.win(AP.outcome.name(b, f, w)) == True{} : Bool}
  {f == True{} : Bool}

def name_fit(b, f, _w, s):
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
  for ss: List<&2, K.Item>
  for +w: A.World
  for s: {M2.win(AP.outcome.entry(g, K.Walked{h, r, fs, ss}, w)) == True{} : Bool}
  {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.dep.of(h, r, w))) == True{} : Bool}

def entry_fit(g, h, r, _fs, _ss, w, s):
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
      entry_fit(M2.got(w), h, r, fs, ss, w,
        Equal.cong(P.Outcome, Bool, o => M2.win(o), AP.outcome.k(K.Walked{h, r, fs, ss}, w),
          P.Success{}, s))
    case K.Asks{at}:
      Eq.bit.absurd(&2, {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)),
        AP.added.k(K.Asks{at}, w))) == True{} : Bool},
        Equal.trans(Bool, False{}, M2.win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, M2.win(AP.outcome.k(K.Asks{at}, w)), False{},
            M1.asks_loses(M2.got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => M2.win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)),
        AP.added.k(K.Refused{why}, w))) == True{} : Bool},
        Equal.trans(Bool, False{}, M2.win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, M2.win(AP.outcome.k(K.Refused{why}, w)), False{},
            M1.refused_loses(M2.got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => M2.win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

# what a path was written with. Proof vocabulary.
def wrote.text_add(x: P.Wrote) -> String:
  match x:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# An add that does not refuse writes `Rend.add.keep`'s ledger
# (`add_edits_ledger`), whose walk ended in success, so the ledger is
# renderable and the manifest's round trip reads it back.
def Laws.add_ledger_reads_back(w, m, good, ok, text, put, rb):
  +fit = Equal.trans(Bool, Rend.renderable(Rend.add.keep(m, AP.added(w))),
    Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), AP.added(w))), True{},
    Equal.cong(M.Manifest, Bool, x => Rend.renderable(Rend.add.keep(x, AP.added(w))),
      m, A.manifest.of(A.read(w)),
      Equal.sym(M.Manifest, A.manifest.of(A.read(w)), m, M1.good_m(w, m, good))),
    fit_k(AP.walked(w), w, M1.won(w, ok)))
  +p = Equal.trans(P.Wrote, P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))},
    P.put.plan(AP.plan(w), "ez.toml"), P.Put{text},
    Equal.sym(P.Wrote, P.put.plan(AP.plan(w), "ez.toml"),
      P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))}, L1.add_edits_ledger(w, m, good, ok)),
    put)
  +t = Equal.cong(P.Wrote, String, x => wrote.text_add(x),
    P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))}, P.Put{text}, p)
  %t : {M.parse(_) == M.Good{Rend.add.keep(m, AP.added(w))} : M.Read}
  rb(Rend.add.keep(m, AP.added(w)), fit)

# LAW: and one whose ledger would not read back refuses too
law hfit_false:
  for held: Bool
  for +at: String
  for +w: A.World
  for es: List<&2, P.Effect>
  {H.refuses.plan(H.seal(es, H.outcome.entry(held, False{}, at, w))) == True{} : Bool}

def hfit_false(held, _at, _w, _es):
  match held:
    case True{}:
      {==}
    case False{}:
      {==}

law hfit_loses:
  for held: Bool
  for fit: Bool
  for +at: String
  for +w: A.World
  for es: List<&2, P.Effect>
  for e: {fit == False{} : Bool}
  {H.refuses.plan(H.seal(es, H.outcome.entry(held, fit, at, w))) == True{} : Bool}

def hfit_loses(held, fit, at, w, es, e):
  match fit:
    case True{}:
      Eq.bit.absurd2(&2, {H.refuses.plan(H.seal(es, H.outcome.entry(held, True{}, at, w)))
        == True{} : Bool}, e)
    case False{}:
      hfit_false(held, at, w, es)

# LAW: a hub plan whose ledger would not read back refuses
law hv_unfit:
  for v: H.Verdict
  for +w: A.World
  for bad: {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)),
    H.dep.of(H.verdict.hash(v), H.verdict.files(v), w))) == False{} : Bool}
  {H.refuses.plan(H.plan.v(v, w)) == True{} : Bool}

def hv_unfit(v, w, bad):
  match v:
    case H.Go{+h, +fs, +ss}:
      hfit_loses(Bool.or(String.is_empty(H.asked(w)), H.holds(fs, Path.norm(H.asked(w)))),
        Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), H.dep.of(h, fs, w))),
        H.asked(w), w,
        H.effects.of(H.dep.of(h, fs, w), h, W.laid(fs, ss), A.manifest.of(A.read(w)), w), bad)
    case H.Pending{_asks}:
      {==}
    case H.Stop{_why}:
      {==}

def Laws.add_named_refuses_unrenderable(w, bad):
  hv_unfit(H.decide(w), w, bad)

# LAW: and its outcome is a success
law hseal_outcome:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for ok: {H.refuses.plan(H.seal(es, o)) == False{} : Bool}
  {o == P.Success{} : P.Outcome}

def hseal_outcome(_es, o, ok):
  match o:
    case P.Success{}:
      {==}
    case P.Refused{why}:
      Eq.bit.absurd2(&2, {P.Refused{why} == P.Success{} : P.Outcome}, ok)

# LAW: and its outcome is a success
law hwon:
  for +w: A.World
  for ok: {H.refuses(w) == False{} : Bool}
  {M2.hout(w) == P.Success{} : P.Outcome}

def hwon(w, ok):
  hseal_outcome(M2.heff(w), M2.hout(w), M2.hmade_ok(w, ok))

# LAW: a hub add's outcome that is a success found its ledger renderable
law hentry_fit:
  for held: Bool
  for fit: Bool
  for +at: String
  for +w: A.World
  for s: {M2.win(H.outcome.entry(held, fit, at, w)) == True{} : Bool}
  {fit == True{} : Bool}

def hentry_fit(held, fit, _at, _w, s):
  match held fit:
    case True{} True{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, s)
    case False{} _:
      Eq.bit.absurd(&2, {fit == True{} : Bool}, s)

# An add that does not refuse writes `Rend.add.keep`'s ledger, whose outcome
# was a success, so the ledger is renderable and reads back.
def Laws.add_named_reads_back(w, m, good, ok, text, put, rb):
  +fit = Equal.trans(Bool, Rend.renderable(Rend.add.keep(m, H.added(w))),
    Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), H.added(w))), True{},
    Equal.cong(M.Manifest, Bool, x => Rend.renderable(Rend.add.keep(x, H.added(w))),
      m, A.manifest.of(A.read(w)),
      Equal.sym(M.Manifest, A.manifest.of(A.read(w)), m, M1.good_m(w, m, good))),
    hentry_fit(Bool.or(String.is_empty(H.asked(w)), H.holds(H.files(w), Path.norm(H.asked(w)))),
      Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), H.added(w))), H.asked(w), w,
      Equal.cong(P.Outcome, Bool, o => M2.win(o), M2.hout(w), P.Success{}, hwon(w, ok))))
  +p = Equal.trans(P.Wrote, P.Put{Rend.show(Rend.add.keep(m, H.added(w)))},
    P.put.plan(H.plan(w), "ez.toml"), P.Put{text},
    Equal.sym(P.Wrote, P.put.plan(H.plan(w), "ez.toml"),
      P.Put{Rend.show(Rend.add.keep(m, H.added(w)))},
      L1.add_named_edits_ledger(w, m, good, ok)),
    put)
  +t = Equal.cong(P.Wrote, String, x => wrote.text_add(x),
    P.Put{Rend.show(Rend.add.keep(m, H.added(w)))}, P.Put{text}, p)
  %t : {M.parse(_) == M.Good{Rend.add.keep(m, H.added(w))} : M.Read}
  rb(Rend.add.keep(m, H.added(w)), fit)

# whether a path was written, and what with. Proof vocabulary.
def wrote.is(w: P.Wrote) -> Bool:
  match w:
    case P.Kept{}:
      False{}
    case P.Put{_t}:
      True{}

def wrote.text_init(w: P.Wrote) -> String:
  match w:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# LAW: a path left as it was is not one written
law kept_not_put:
  for +text: String
  for e: {P.Kept{} == P.Put{text} : P.Wrote}
  {wrote.is(P.Kept{}) == True{} : Bool}

def kept_not_put(text, e):
  Equal.cong(P.Wrote, Bool, w => wrote.is(w), P.Kept{}, P.Put{text}, e)

# LAW: the stub, with whether the entry is ez.toml given, is never written
# over ez.toml
law stub_kept.go:
  for +at: String
  for +text: String
  for +b: Bool
  for eb: {String.eq(at, "ez.toml") == b : Bool}
  for +c: Bool
  {P.put.in(IP.main.put(Bool.not(Bool.or(b, c)), at, text, []), "ez.toml") == P.Kept{} : P.Wrote}

def stub_kept.go(at, text, b, eb, c):
  match b c:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      %Equal.sym(Bool, String.eq(at, "ez.toml"), False{}, eb)
        : {Bool.pick(P.Wrote, _, P.Put{text}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}

# LAW: the stub, when it is due, is not written over ez.toml
law main_kept:
  for +mn: Maybe<&2, String>
  for +at: String
  for +text: String
  {P.put.in(IP.main.put(IP.due(mn, at), at, text, []), "ez.toml") == P.Kept{} : P.Wrote}

def main_kept(mn, at, text):
  match mn:
    case Some{_s}:
      {==}
    case None{}:
      stub_kept.go(at, text, String.eq(at, "ez.toml"), {==}, String.eq(at, ".gitignore"))

# LAW: the library, laid out or not, is not written over ez.toml, and leaves
# it to the stub
law lib_kept:
  for +l: Bool
  for +mn: Maybe<&2, String>
  for +at: String
  for +text: String
  {P.put.in(IP.lib.put(l, IP.main.put(IP.due(mn, at), at, text, [])), "ez.toml") == P.Kept{} : P.Wrote}

def lib_kept(l, mn, at, text):
  match l:
    case True{}:
      %Equal.sym(P.Wrote, P.put.in(IP.main.put(IP.due(mn, at), at, text, []), "ez.toml"), P.Kept{},
        main_kept(mn, at, text))
        : {P.put.one(P.Write{"src/lib.bend", IP.lib()}, "ez.toml", _) == P.Kept{} : P.Wrote}
      {==}
    case False{}:
      main_kept(mn, at, text)

# LAW: nor is anything else a new project writes after its ledger
law rest_kept_init:
  for +ms: List<&2, String>
  for +text: String
  for +name: String
  for +at: String
  for +desc: String
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  {P.put.in(IP.ignore.put(ms, text, IP.files(name, at, desc, mn, lb)), "ez.toml") == P.Kept{} : P.Wrote}

def rest_kept_init(ms, text, name, at, desc, mn, lb):
  %Equal.sym(P.Wrote, P.put.in(IP.ignore.put(ms, text, IP.files(name, at, desc, mn, lb)), "ez.toml"),
    P.put.in(IP.files(name, at, desc, mn, lb), "ez.toml"),
    M3.ignore_passes(ms, text, IP.files(name, at, desc, mn, lb), "ez.toml", {==}))
    : {_ == P.Kept{} : P.Wrote}
  lib_kept(IP.lays(lb, IP.due(mn, at), at), mn, at, IP.stub(name, desc, IP.lays(lb, IP.due(mn, at), at)))

# LAW: a new project's plan writes to ez.toml a ledger that reads back as the
# one it made
law new_reads:
  for +ok: Bool
  for +name: String
  for +at: String
  for +desc: String
  for eok: {IP.fits(name, at, desc) == ok : Bool}
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  for +text: String
  for put: {P.put.plan(IP.plan.new(ok, name, at, desc, ig, mn, lb), "ez.toml") == P.Put{text} : P.Wrote}
  for rb: D1.ReadsBack()
  {M.parse(text) == M.Good{IP.model(name, at)} : M.Read}

def new_reads(ok, name, at, desc, eok, ig, mn, lb, text, put, rb):
  match ok:
    case False{}:
      Eq.bit.absurd(&2, {M.parse(text) == M.Good{IP.model(name, at)} : M.Read},
        kept_not_put(text, put))
    case True{}:
      +k = rest_kept_init(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig), name, at, desc,
        mn, lb)
      +p = Equal.trans(P.Wrote, P.Put{IP.fresh(name, at)},
        P.put.plan(IP.plan.new(True{}, name, at, desc, ig, mn, lb), "ez.toml"), P.Put{text},
        Equal.sym(P.Wrote, P.put.plan(IP.plan.new(True{}, name, at, desc, ig, mn, lb), "ez.toml"),
          P.Put{IP.fresh(name, at)},
          Equal.cong(P.Wrote, P.Wrote, w => P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, "ez.toml", w),
            P.put.in(IP.ignore.put(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))),
              IP.text.of(ig), IP.files(name, at, desc, mn, lb)), "ez.toml"), P.Kept{}, k)),
        put)
      +t = Equal.cong(P.Wrote, String, w => wrote.text_init(w), P.Put{IP.fresh(name, at)}, P.Put{text}, p)
      %t : {M.parse(_) == M.Good{IP.model(name, at)} : M.Read}
      rb(IP.model(name, at),
        Eq.and.left(Rend.renderable(IP.model(name, at)), Bool.not(B.has.nl(IP.header(name, desc))), eok))

# A ledger that is there leaves ez.toml as it was; one that is not is the
# ledger the plan made, which it writes only once the project fits.
def Laws.init_ledger_reads_back(n, e, d, led, ig, mn, lb, text, put, rb):
  match led:
    case Some{_s}:
      Eq.bit.absurd(&2, {M.parse(text) == M.Good{IP.model(IP.name.or(n), IP.entry.or(e))} : M.Read},
        kept_not_put(text, put))
    case None{}:
      new_reads(IP.fits(IP.name.or(n), IP.entry.or(e), d),
        IP.name.or(n), IP.entry.or(e), d, {==}, ig, mn, lb, text, put, rb)

# ---------------------------------------------------------------------------
# laws/WrittenLedgerReadsBack.bend

# what a path was written with. Proof vocabulary.
def wrote.text_remove(w: P.Wrote) -> String:
  match w:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# LAW: a plan over a ledger that does not refuse was given True
law has_ok:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for ok: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == False{} : Bool}
  {h == True{} : Bool}

def has_ok(h, _m, _name, _ignore, ok):
  match h:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, ok)

# A remove that does not refuse writes `Rend.remove`'s ledger, which it made
# sure is renderable, so the manifest's round trip reads it back.
def Laws.remove_ledger_reads_back(name, s, ignore, m, text, good, ok, put, rb):
  +ok2 = Equal.trans(Bool,
    RP.refuses.plan(RP.plan.read(M.Good{m}, name, ignore)),
    RP.refuses.plan(RP.plan.read(M.parse(s), name, ignore)),
    False{},
    Equal.cong(M.Read, Bool, x => RP.refuses.plan(RP.plan.read(x, name, ignore)),
      M.Good{m}, M.parse(s), good),
    ok)
  +er = Eq.and.right(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name)),
    has_ok(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))),
      m, name, ignore, ok2))
  +p = Equal.trans(P.Wrote, P.Put{Rend.show(Rend.remove(m, name))},
    P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml"), P.Put{text},
    Equal.sym(P.Wrote, P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml"),
      P.Put{Rend.show(Rend.remove(m, name))}, L2.remove_edits_ledger(name, s, ignore, m, good, ok)),
    put)
  +t = Equal.cong(P.Wrote, String, w => wrote.text_remove(w), P.Put{Rend.show(Rend.remove(m, name))},
    P.Put{text}, p)
  %t : {M.parse(_) == M.Good{Rend.remove(m, name)} : M.Read}
  rb(Rend.remove(m, name), er)
