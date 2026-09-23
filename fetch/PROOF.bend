# fetch: the proofs. `bend PROOF.bend` is the gate.
#
# The plan is `plan.led(ledger, lock, w)`: no ledger, then no lock, is a plan
# with no effect, and otherwise the plan is `plan.parts` of every package of
# the lock, which seals the effects of the verdicts with how they end. A
# sealed plan that refuses has no effect, so the refusal law is case splits.
# Every law about what a fetch lays is a law about `effects.of` over the
# verdicts, and a verdict lays a tree only in the arm where `good` answered
# True of the files it lays, so it is carried by induction over the lock's
# hashes with `good`'s answer as the one premise. The questions are the same
# walk over the lock's hashes, and a package asks for a checkout only through
# `fetch.ask` of the source the lock records for it.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./world.bend as F
import ./plan.bend as FP
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/lock.bend as L
import ../add/plan.bend as AP
import ../add/PROOF.bend as AddP
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../sha/sha.bend as Sha
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# ---------------------------------------------------------------------------
# refusals

# LAW: a sealed plan that refuses writes nothing
law seal_quiet:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for r: {FP.refuses.plan(FP.seal(es, o)) == True{} : Bool}
  {P.writes(FP.seal(es, o)) == False{} : Bool}

def seal_quiet(es, o, r):
  match o:
    case P.Success{}:
      Eq.bit.absurd(&2, {P.writes(FP.seal(es, P.Success{})) == False{} : Bool}, r)
    case P.Refused{_why}:
      {==}

# LAW: nor does a plan for a ledger and a lock, there or not
law led_quiet:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  for r: {FP.refuses.plan(FP.plan.led(b, g, w)) == True{} : Bool}
  {P.writes(FP.plan.led(b, g, w)) == False{} : Bool}

def led_quiet(b, g, w, r):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          seal_quiet(FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
            FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))), r)

def Laws.fetch_refusal_writes_nothing(w, r):
  led_quiet(F.ledger(w), F.lock(w), w, r)

# No ledger is the arm that refuses before anything else.
def Laws.fetch_needs_ledger(_here, _got, _rs):
  {==}

def Laws.fetch_needs_ledger_asks_nothing(_here, _got, _rs):
  {==}

# No lock refuses whether or not there is a ledger.
def Laws.fetch_needs_lock(_here, led, _rs):
  match led:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.fetch_needs_lock_asks_nothing(_here, led, _rs):
  match led:
    case False{}:
      {==}
    case True{}:
      {==}

# ---------------------------------------------------------------------------
# the trees laid

# LAW: all but the last of a list with one more at its end is the list
law front_snoc:
  for xs: List<&2, W.Source>
  for x: W.Source
  {FP.front(List.append(&2, W.Source, xs, [x])) == xs : List<&2, W.Source>}

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
            FP.front(List.append(&2, W.Source, h2 <> t2, [x])), h2 <> t2,
            front_snoc(h2 <> t2, x))

# LAW: a sealed plan's effects are the ones it was given, or none
law locked_seal:
  for +ss: List<&2, T.Sect>
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {FP.lays.locked(ss, es) == True{} : Bool}
  {FP.lays.locked(ss, FP.effects(FP.seal(es, o))) == True{} : Bool}

def locked_seal(_ss, _es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

# LAW: files that passed `good`, laid, are the files the lock records
law locked_got:
  for b: Bool
  for +ss: List<&2, T.Sect>
  for +h: String
  for +ls: List<&2, W.Source>
  for rest: List<&2, P.Effect>
  for g: {FP.good(FP.locked(ss, h), h, ls) == b : Bool}
  for e: {FP.lays.locked(ss, rest) == True{} : Bool}
  {FP.lays.locked(ss, FP.effect.v(FP.judge.got(b, FP.locked(ss, h), h, ls), rest))
    == True{} : Bool}

def locked_got(b, ss, h, ls, rest, g, e):
  match b:
    case False{}:
      e
    case True{}:
      %Equal.sym(List<&2, W.Source>,
        FP.front(List.append(&2, W.Source, ls, [W.Source{"manifest", FP.manifest(ls)}])),
        ls, front_snoc(ls, W.Source{"manifest", FP.manifest(ls)}))
        : {Bool.and(FP.fits(FP.locked(ss, h), _), FP.lays.locked(ss, rest)) == True{}
          : Bool}
      %Equal.sym(Bool, FP.fits(FP.locked(ss, h), ls), True{},
        Eq.and.left(FP.fits(FP.locked(ss, h), ls),
          Bool.and(FP.paths.safe(ls), String.eq(h, FP.named(ls))), g))
        : {Bool.and(_, FP.lays.locked(ss, rest)) == True{} : Bool}
      e

# LAW: so does every verdict on a package of the lock, wherever it stands
law locked_one:
  for +ss: List<&2, T.Sect>
  for +h: String
  for p: FP.Part
  for rest: List<&2, P.Effect>
  for e: {FP.lays.locked(ss, rest) == True{} : Bool}
  {FP.lays.locked(ss, FP.effect.v(FP.judge(FP.locked(ss, h), h, p), rest)) == True{}
    : Bool}

def locked_one(ss, h, p, rest, e):
  match p:
    case FP.AskLaid{}:
      e
    case FP.AskFetch{}:
      e
    case FP.Have{}:
      e
    case FP.Got{+ls}:
      locked_got(FP.good(FP.locked(ss, h), h, ls), ss, h, ls, rest, {==}, e)
    case FP.No{_why}:
      e

# LAW: and so do the verdicts on every package of the lock
law locked_all:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +hub: String
  for hs: List<&2, String>
  {FP.lays.locked(ss, FP.effects.of(FP.judged(FP.parts(ss, rs, here, hub, hs)))) == True{}
    : Bool}

def locked_all(ss, rs, here, hub, hs):
  match hs:
    case []:
      {==}
    case +h <> +t:
      locked_one(ss, h,
        FP.part(rs, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), here, hub, h),
        FP.effects.of(FP.judged(FP.parts(ss, rs, here, hub, t))),
        locked_all(ss, rs, here, hub, t))

law locked_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  {FP.lays.locked(F.sects(w), FP.effects(FP.plan.led(b, g, w))) == True{} : Bool}

def locked_led(b, g, w):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          locked_seal(F.sects(w),
            FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
            FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
            locked_all(F.sects(w), F.replies(w), F.here(w), L.lock.hub(F.sects(w)),
              L.hashes(F.sects(w))))

def Laws.fetch_lays_the_lock(w):
  locked_led(F.ledger(w), F.lock(w), w)

# ---------------------------------------------------------------------------
# the trees are named

# LAW: the planner weighs a file the way the law vocabulary does
law weighs_same:
  for ls: List<&2, W.Source>
  {FP.weighs(ls) == AP.weighs(ls) : List<&2, K.File>}

def weighs_same(ls):
  match ls:
    case []:
      {==}
    case W.Source{at, text} <> t:
      Equal.cong(List<&2, K.File>, List<&2, K.File>, ys => K.File{at, Sha.hex(text)} <> ys,
        FP.weighs(t), AP.weighs(t), weighs_same(t))

law named_seal:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {AP.lays.named(es) == True{} : Bool}
  {AP.lays.named(FP.effects(FP.seal(es, o))) == True{} : Bool}

def named_seal(_es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

# LAW: files that passed `good`, laid with their manifest last, are named by
# it
law named_got:
  for b: Bool
  for +fs: List<&2, K.File>
  for +h: String
  for +ls: List<&2, W.Source>
  for rest: List<&2, P.Effect>
  for g: {FP.good(fs, h, ls) == b : Bool}
  for e: {AP.lays.named(rest) == True{} : Bool}
  {AP.lays.named(FP.effect.v(FP.judge.got(b, fs, h, ls), rest)) == True{} : Bool}

def named_got(b, fs, h, ls, rest, g, e):
  match b:
    case False{}:
      e
    case True{}:
      %Equal.sym(List<&2, W.Source>,
        AP.front(List.append(&2, W.Source, ls, [W.Source{"manifest", FP.manifest(ls)}])),
        ls, AddP.front_snoc(ls, W.Source{"manifest", FP.manifest(ls)}))
        : {Bool.and(Bool.and(String.eq(h, K.hash_of(K.files_of(AP.weighs(_)))),
          String.eq(AP.last(List.append(&2, W.Source, ls,
            [W.Source{"manifest", FP.manifest(ls)}])),
            K.manifest_of(K.files_of(AP.weighs(_))))), AP.lays.named(rest)) == True{}
          : Bool}
      %weighs_same(ls)
        : {Bool.and(Bool.and(String.eq(h, K.hash_of(K.files_of(_))),
          String.eq(AP.last(List.append(&2, W.Source, ls,
            [W.Source{"manifest", FP.manifest(ls)}])),
            K.manifest_of(K.files_of(_)))), AP.lays.named(rest)) == True{} : Bool}
      %Equal.sym(String,
        AP.last(List.append(&2, W.Source, ls, [W.Source{"manifest", FP.manifest(ls)}])),
        FP.manifest(ls), AddP.last_snoc(ls, "manifest", FP.manifest(ls)))
        : {Bool.and(Bool.and(String.eq(h, FP.named(ls)), String.eq(_, FP.manifest(ls))),
          AP.lays.named(rest)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(FP.manifest(ls), FP.manifest(ls)), True{},
        Eq.string_eq_self(FP.manifest(ls)))
        : {Bool.and(Bool.and(String.eq(h, FP.named(ls)), _), AP.lays.named(rest)) == True{}
          : Bool}
      %Equal.sym(Bool, String.eq(h, FP.named(ls)), True{},
        Eq.and.right(FP.paths.safe(ls), String.eq(h, FP.named(ls)),
          Eq.and.right(FP.fits(fs, ls),
            Bool.and(FP.paths.safe(ls), String.eq(h, FP.named(ls))), g)))
        : {Bool.and(Bool.and(_, True{}), AP.lays.named(rest)) == True{} : Bool}
      e

law named_one:
  for +fs: List<&2, K.File>
  for +h: String
  for p: FP.Part
  for rest: List<&2, P.Effect>
  for e: {AP.lays.named(rest) == True{} : Bool}
  {AP.lays.named(FP.effect.v(FP.judge(fs, h, p), rest)) == True{} : Bool}

def named_one(fs, h, p, rest, e):
  match p:
    case FP.AskLaid{}:
      e
    case FP.AskFetch{}:
      e
    case FP.Have{}:
      e
    case FP.Got{+ls}:
      named_got(FP.good(fs, h, ls), fs, h, ls, rest, {==}, e)
    case FP.No{_why}:
      e

law named_all:
  for ps: List<&2, FP.Pt>
  {AP.lays.named(FP.effects.of(FP.judged(ps))) == True{} : Bool}

def named_all(ps):
  match ps:
    case []:
      {==}
    case FP.Pt{h, _src, fs, p} <> +t:
      named_one(fs, h, p, FP.effects.of(FP.judged(t)), named_all(t))

law named_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  {AP.lays.named(FP.effects(FP.plan.led(b, g, w))) == True{} : Bool}

def named_led(b, g, w):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          named_seal(FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
            FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
            named_all(FP.parts.of(F.sects(w), w)))

def Laws.fetch_lays_named(w):
  named_led(F.ledger(w), F.lock(w), w)

# ---------------------------------------------------------------------------
# no file is written

law kept_all:
  for vs: List<&2, FP.Verdict>
  for +path: String
  {P.put.in(FP.effects.of(vs), path) == P.Kept{} : P.Wrote}

def kept_all(vs, path):
  match vs:
    case []:
      {==}
    case v <> +t:
      match v:
        case FP.Keep{}:
          kept_all(t, path)
        case FP.Put{_hash, _ls}:
          kept_all(t, path)
        case FP.Stop{_why}:
          kept_all(t, path)

law kept_seal:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for +path: String
  for e: {P.put.in(es, path) == P.Kept{} : P.Wrote}
  {P.put.plan(FP.seal(es, o), path) == P.Kept{} : P.Wrote}

def kept_seal(_es, o, _path, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

law kept_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  for +path: String
  {P.put.plan(FP.plan.led(b, g, w), path) == P.Kept{} : P.Wrote}

def kept_led(b, g, w, path):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          kept_seal(FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
            FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))), path,
            kept_all(FP.judged(FP.parts.of(F.sects(w), w)), path))

def Laws.fetch_keeps_records(w, path):
  kept_led(F.ledger(w), F.lock(w), w, path)

# ---------------------------------------------------------------------------
# the questions

# LAW: the question that fetches a package asks for it from the source the
# lock records, anchored at `here`
law fetch_ask_anchored:
  for s: L.Src
  for +here: String
  for +hub: String
  for +h: String
  for +ss: List<&2, T.Sect>
  for q: {L.pack.src(L.pack_of(ss, h)) == s : L.Src}
  {FP.ask.anchored(here, L.pack.src(L.pack_of(ss, FP.ask.hash(FP.fetch.ask(s, here, hub, h)))),
    FP.fetch.ask(s, here, hub, h)) == True{} : Bool}

def fetch_ask_anchored(s, here, _hub, h, ss, q):
  match s:
    case L.Hub{}:
      {==}
    case L.Git{url, rev, entry, root, nar, tag}:
      %Equal.sym(L.Src, L.pack.src(L.pack_of(ss, h)), L.Git{url, rev, entry, root, nar, tag}, q)
        : {String.eq(Path.anchor(here, url), Path.anchor(here, L.src.url(_))) == True{} : Bool}
      Eq.string_eq_self(Path.anchor(here, url))

# LAW: so is every question one package asks
law asks_one:
  for +here: String
  for +hub: String
  for +h: String
  for +ss: List<&2, T.Sect>
  for p: FP.Part
  for rest: List<&2, F.Ask>
  for e: {FP.asks.anchored(here, ss, rest) == True{} : Bool}
  {FP.asks.anchored(here, ss,
    FP.ask.pt(FP.Pt{h, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), p}, here, hub, rest))
    == True{} : Bool}

def asks_one(here, hub, h, ss, p, rest, e):
  match p:
    case FP.AskLaid{}:
      e
    case FP.AskFetch{}:
      %Equal.sym(Bool,
        FP.ask.anchored(here,
          L.pack.src(L.pack_of(ss,
            FP.ask.hash(FP.fetch.ask(L.pack.src(L.pack_of(ss, h)), here, hub, h)))),
          FP.fetch.ask(L.pack.src(L.pack_of(ss, h)), here, hub, h)),
        True{},
        fetch_ask_anchored(L.pack.src(L.pack_of(ss, h)), here, hub, h, ss, {==}))
        : {Bool.and(_, FP.asks.anchored(here, ss, rest)) == True{} : Bool}
      e
    case FP.Have{}:
      e
    case FP.Got{_ls}:
      e
    case FP.No{_why}:
      e

# LAW: and so is every question of every package of the lock
law asks_all:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +hub: String
  for hs: List<&2, String>
  {FP.asks.anchored(here, ss, FP.asks.of(FP.parts(ss, rs, here, hub, hs), here, hub))
    == True{} : Bool}

def asks_all(ss, rs, here, hub, hs):
  match hs:
    case []:
      {==}
    case +h <> +t:
      asks_one(here, hub, h, ss,
        FP.part(rs, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), here, hub, h),
        FP.asks.of(FP.parts(ss, rs, here, hub, t), here, hub),
        asks_all(ss, rs, here, hub, t))

law asks_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  {FP.asks.anchored(F.here(w), F.sects(w), FP.wants.led(b, g, w)) == True{} : Bool}

def asks_led(b, g, w):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          asks_all(F.sects(w), F.replies(w), F.here(w), L.lock.hub(F.sects(w)),
            L.hashes(F.sects(w)))

def Laws.fetch_asks_anchored(w):
  asks_led(F.ledger(w), F.lock(w), w)
