# proofs of laws/AddEntryChosen.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/git/git.bend as Git
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../laws/AddEntryChosen.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2
import ./lemmas/PlanEffectFacts.bend as M3

# The walk.

# LAW: the first step of a walk over a whole checkout, whose entry is inside
# it and not held, stops on the entry with nothing found and nothing queued
law first_step_stops:
  for +eb: String
  for +entry: String
  for +fs: List<&2, K.Source>
  for inside: {False{} == K.outside(entry) : Bool}
  for miss: {None{} == K.look(fs, entry) : Maybe<&2, String>}
  {K.step(K.Tree{True{}, fs, []}, eb, K.start(entry))
    == K.State{[], [], K.Missing{entry}, []} : K.State}

def first_step_stops(eb, entry, fs, inside, miss):
  %inside : {K.visit.in(_, K.Tree{True{}, fs, []}, entry, "", eb, [], [], [])
    == K.State{[], [], K.Missing{entry}, []} : K.State}
  %miss : {K.visit.have(K.find.got(_, True{}, [], entry), K.Tree{True{}, fs, []},
    entry, "", eb, [], [], [])
    == K.State{[], [], K.Missing{entry}, []} : K.State}
  {==}

# LAW: a walk that has stopped on a missing file stays stopped, whatever
# fuel is left
law missing_stays:
  for f: Nat
  for +tree: K.Tree
  for +eb: String
  for +at: String
  {K.walk(f, tree, eb, K.State{[], [], K.Missing{at}, []})
    == K.State{[], [], K.Missing{at}, []} : K.State}

def missing_stays(f, _tree, _eb, _at):
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# LAW: so the whole walk ends where the first step stopped
law walk_stops:
  for f: Nat
  for +entry: String
  for +fs: List<&2, K.Source>
  for inside: {False{} == K.outside(entry) : Bool}
  for miss: {None{} == K.look(fs, entry) : Maybe<&2, String>}
  {K.walk((1n + f : Nat), K.Tree{True{}, fs, []}, Path.base(entry), K.start(entry))
    == K.State{[], [], K.Missing{entry}, []} : K.State}

def walk_stops(f, entry, fs, inside, miss):
  Equal.trans(K.State,
    K.walk(f, K.Tree{True{}, fs, []}, Path.base(entry),
      K.step(K.Tree{True{}, fs, []}, Path.base(entry), K.start(entry))),
    K.walk(f, K.Tree{True{}, fs, []}, Path.base(entry),
      K.State{[], [], K.Missing{entry}, []}),
    K.State{[], [], K.Missing{entry}, []},
    Equal.cong(K.State, K.State,
      s => K.walk(f, K.Tree{True{}, fs, []}, Path.base(entry), s),
      K.step(K.Tree{True{}, fs, []}, Path.base(entry), K.start(entry)),
      K.State{[], [], K.Missing{entry}, []},
      first_step_stops(Path.base(entry), entry, fs, inside, miss)),
    missing_stays(f, K.Tree{True{}, fs, []}, Path.base(entry), entry))

def Laws.absent_entry_refused(f, entry, fs, inside, miss):
  Equal.cong(K.State, K.Walked, s => K.made.all(K.Tree{True{}, fs, []}, entry, s),
    K.walk((1n + f : Nat), K.Tree{True{}, fs, []}, Path.base(entry), K.start(entry)),
    K.State{[], [], K.Missing{entry}, []},
    walk_stops(f, entry, fs, inside, miss))

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
      AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok)),
    entry_default(w, none))

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
  for ss: List<&2, K.Item>
  for +m: M.Manifest
  for +w: A.World
  {AP.last.go(P.said.in(AP.effects.of(d, h, a, fs, ss, m, w)), "") == Git.import.line(h, a)
    : String}

def says_of(d, h, a, _fs, _ss, m, w):
  %Equal.sym(List<&2, String>,
    P.said.in(AP.ignore.put(String.eq(M2.nxt(d, m, w), A.ignore(w)), M2.nxt(d, m, w),
      P.drops.of(M2.gss(d, h, m), AP.says(h, a, w)))),
    P.said.in(P.drops.of(M2.gss(d, h, m), AP.says(h, a, w))),
    ignore_said(String.eq(M2.nxt(d, m, w), A.ignore(w)), M2.nxt(d, m, w),
      P.drops.of(M2.gss(d, h, m), AP.says(h, a, w))))
    : {AP.last.go(_, "") == Git.import.line(h, a) : String}
  %Equal.sym(List<&2, String>, P.said.in(P.drops.of(M2.gss(d, h, m), AP.says(h, a, w))),
    P.said.in(AP.says(h, a, w)), drops_said(M2.gss(d, h, m), AP.says(h, a, w)))
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
        Equal.trans(Bool, False{}, M2.win(AP.outcome.k(K.Asks{at}, w)), True{},
          Equal.sym(Bool, M2.win(AP.outcome.k(K.Asks{at}, w)), False{},
            M1.asks_loses(M2.got(w), at, w)),
          Equal.cong(P.Outcome, Bool, o => M2.win(o), AP.outcome.k(K.Asks{at}, w),
            P.Success{}, s)))
    case K.Refused{why}:
      Eq.bit.absurd(&2, {AP.last.go(P.said.in(AP.effects.k(K.Refused{why}, w)), "")
        == Git.import.line("", AP.at.of(".", w)) : String},
        Equal.trans(Bool, False{}, M2.win(AP.outcome.k(K.Refused{why}, w)), True{},
          Equal.sym(Bool, M2.win(AP.outcome.k(K.Refused{why}, w)), False{},
            M1.refused_loses(M2.got(w), why, w)),
          Equal.cong(P.Outcome, Bool, o => M2.win(o), AP.outcome.k(K.Refused{why}, w),
            P.Success{}, s)))

def Laws.add_says_import(w, ok):
  %Equal.sym(P.Plan, AP.plan(w), P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    M1.succeeds(w, ok))
    : {AP.last(_) == Git.import.line(AP.hash(w), AP.at(w)) : String}
  says_k(AP.walked(w), w, M1.won(w, ok))

# The lookup is rewritten to the None the premise gives, which is refused.
def entry_loses(
  +w: A.World,
  miss: {None{} == M2.got(w) : Maybe<&2, String>}
) -> {M2.win(AP.outcome.k(AP.walked(w), w)) == False{} : Bool}:
  %miss : {M2.win(AP.outcome.entry(_, AP.walked(w), w)) == False{} : Bool}
  {==}

def Laws.add_entry_absent(w, miss):
  M2.lose_v(AP.decide(w), w, entry_loses(w, miss))

# LAW: an outcome that is the entry's when it is not held refuses
law hentry_loses:
  for held: Bool
  for fit: Bool
  for +at: String
  for +w: A.World
  for es: List<&2, P.Effect>
  for e: {held == False{} : Bool}
  {H.refuses.plan(H.seal(es, H.outcome.entry(held, fit, at, w))) == True{} : Bool}

def hentry_loses(held, fit, at, w, es, e):
  match held:
    case True{}:
      Eq.bit.absurd2(&2, {H.refuses.plan(H.seal(es, H.outcome.entry(True{}, fit, at, w)))
        == True{} : Bool}, e)
    case False{}:
      {==}

# LAW: both halves of an `or` that are False
law or_false_add:
  for x: Bool
  for y: Bool
  for ex: {x == False{} : Bool}
  for ey: {y == False{} : Bool}
  {Bool.or(x, y) == False{} : Bool}

def or_false_add(x, y, ex, ey):
  %Equal.sym(Bool, x, False{}, ex) : {Bool.or(_, y) == False{} : Bool}
  ey

# LAW: a hub plan whose entry asked for is not in the package refuses
law hv_absent:
  for v: H.Verdict
  for +w: A.World
  for given: {String.is_empty(H.asked(w)) == False{} : Bool}
  for miss: {H.holds(H.verdict.files(v), Path.norm(H.asked(w))) == False{} : Bool}
  {H.refuses.plan(H.plan.v(v, w)) == True{} : Bool}

def hv_absent(v, w, given, miss):
  match v:
    case H.Go{+h, +fs, +ss}:
      hentry_loses(Bool.or(String.is_empty(H.asked(w)), H.holds(fs, Path.norm(H.asked(w)))),
        Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), H.dep.of(h, fs, w))),
        H.asked(w), w,
        H.effects.of(H.dep.of(h, fs, w), h, W.laid(fs, ss), A.manifest.of(A.read(w)), w),
        or_false_add(String.is_empty(H.asked(w)), H.holds(fs, Path.norm(H.asked(w))), given, miss))
    case H.Pending{_asks}:
      {==}
    case H.Stop{_why}:
      {==}

def Laws.add_named_entry_absent(w, given, miss):
  hv_absent(H.decide(w), w, given, miss)

# ---------------------------------------------------------------------------
# the entry and the import line (laws/AddEntryChosen.bend)

# LAW: with neither word after the name, none was asked for
law hasked_none:
  for +w: A.World
  for ne: {A.entry.arg(w) == "" : String}
  for nr: {A.ref(w) == "" : String}
  {H.asked(w) == "" : String}

def hasked_none(w, ne, nr):
  %Equal.sym(String, A.entry.arg(w), "", ne)
    : {Bool.pick(String, String.is_empty(_), A.ref(w), _) == "" : String}
  %Equal.sym(String, A.ref(w), "", nr)
    : {Bool.pick(String, True{}, _, "") == "" : String}
  {==}

def Laws.add_named_entry_default(w, ne, nr):
  %Equal.sym(String, H.asked(w), "", hasked_none(w, ne, nr))
    : {H.entry.pick(String.is_empty(_), H.files(w), _) == H.entry.of(H.files(w)) : String}
  {==}

# LAW: the lines a hub add tells end with the import line when there is an
# entry
law hsays_last:
  for c: Bool
  for +a: String
  for +b: String
  for e: {c == False{} : Bool}
  {H.last.go(P.said.in(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{a}, P.Say{b}])), "")
    == b : String}

def hsays_last(c, a, b, e):
  match c:
    case True{}:
      Eq.bit.absurd2(&2, {H.last.go(P.said.in(Bool.pick(List<&2, P.Effect>, True{}, [P.Say{a}],
        [P.Say{a}, P.Say{b}])), "") == b : String}, e)
    case False{}:
      {==}

# LAW: `.gitignore`'s write says nothing
law hignore_said:
  for b: Bool
  for +next: String
  for rest: List<&2, P.Effect>
  {P.said.in(H.ignore.put(b, next, rest)) == P.said.in(rest) : List<&2, String>}

def hignore_said(b, _next, _rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.add_named_says_import(w, ok, some):
  %Equal.sym(P.Plan, H.plan(w), P.Plan{M2.heff(w), P.Success{}}, M2.hsucceeds(w, ok))
    : {H.last(_) == Git.import.line(A.target(w), Path.norm(M.dep.entry(H.added(w)))) : String}
  %Equal.sym(List<&2, String>,
    P.said.in(H.ignore.put(M2.hsame(w), M2.hnext(w), H.says(H.hash(w), M.dep.entry(H.added(w)), w))),
    P.said.in(H.says(H.hash(w), M.dep.entry(H.added(w)), w)),
    hignore_said(M2.hsame(w), M2.hnext(w), H.says(H.hash(w), M.dep.entry(H.added(w)), w)))
    : {H.last.go(_, "") == Git.import.line(A.target(w), Path.norm(M.dep.entry(H.added(w))))
      : String}
  hsays_last(String.is_empty(M.dep.entry(H.added(w))), A.target(w) ++ " is " ++ H.hash(w),
    Git.import.line(A.target(w), Path.norm(M.dep.entry(H.added(w)))), some)

# Each emptiness the premises give is rewritten into the arm it picks.
def Laws.entry_pick_entry(file, binary, e):
  %e : {Git.entry.bin(_, file, binary) == file : String}
  {==}

def Laws.entry_pick_bin(file, binary, e0, e1):
  %e0 : {Git.entry.bin(_, file, binary) == binary : String}
  %e1 : {Git.entry.main(_, binary) == binary : String}
  {==}

def Laws.entry_pick_main(file, binary, e0, e1):
  %e0 : {Git.entry.bin(_, file, binary) == "main.bend" : String}
  %e1 : {Git.entry.main(_, binary) == "main.bend" : String}
  {==}
