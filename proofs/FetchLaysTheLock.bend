# proofs of laws/FetchLaysTheLock.bend
#
# The plan is `plan.led(ledger, lock, w)`: no ledger, then no lock, is a
# plan with no effect, and otherwise the plan is `parts.plan` of every
# package of the lock, which seals the effects of the verdicts with how they
# end. A sealed plan that refuses has no effect, so the refusal law is case
# splits. Every law about what a fetch lays is a law about `effects.of` over
# the verdicts, and a verdict lays a tree only in the arm where `good`
# answered True of the files it lays, so it is carried by induction over the
# lock's hashes with `good`'s answer as the one premise. The questions are
# the same walk over the lock's hashes, and a package asks for a checkout
# only through `fetch.ask` of the source the lock records for it.
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../src/toml/toml.bend as T
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/FetchLaysTheLock.bend as Laws

# ---------------------------------------------------------------------------
# the trees laid

# LAW: all but the last of a list with one more at its end is the list
law front_snoc_fetch:
  for xs: List<&2, W.Source>
  for x: W.Source
  {FP.front(List.append(&2, W.Source, xs, [x])) == xs : List<&2, W.Source>}

def front_snoc_fetch(xs, x):
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
            front_snoc_fetch(h2 <> t2, x))

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
        ls, front_snoc_fetch(ls, W.Source{"manifest", FP.manifest(ls)}))
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
        FP.weigh.part(FP.weighed(ss, rs, here, h),
          FP.part(rs, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), here, hub, h)),
        FP.effects.of(FP.judged(FP.parts(ss, rs, here, hub, t))),
        locked_all(ss, rs, here, hub, t))

# The names files a fetch lays go ahead of its trees. A names file is no
# tree and no path of the project, so each law about what a fetch lays holds
# of the trees behind them as it held of the trees alone.

# LAW: one names file written, with or without the line that says it was
# rewritten, in front of trees the lock records
law locked_put:
  for b: Bool
  for +ss: List<&2, T.Sect>
  for +nv: String
  for +hash: String
  for was: String
  for +rest: List<&2, P.Effect>
  for e: {FP.lays.locked(ss, rest) == True{} : Bool}
  {FP.lays.locked(ss, FP.name.put.at(b, nv, hash, was, rest)) == True{} : Bool}

def locked_put(b, _ss, _nv, _hash, _was, _rest, e):
  match b:
    case True{}:
      e
    case False{}:
      e

# LAW: every names file, so
law locked_names:
  for +ss: List<&2, T.Sect>
  for ms: List<&2, FP.Nm>
  for +rest: List<&2, P.Effect>
  for e: {FP.lays.locked(ss, rest) == True{} : Bool}
  {FP.lays.locked(ss, FP.names.lay(ms, rest)) == True{} : Bool}

def locked_names(ss, ms, rest, e):
  match ms:
    case []:
      e
    case m <> +t:
      match m:
        case FP.NmPut{+nv, +hash, +was}:
          locked_put(String.is_empty(was), ss, nv, hash, was, FP.names.lay(t, rest),
            locked_names(ss, t, rest, e))
        case FP.NmAsk{_nv}:
          locked_names(ss, t, rest, e)
        case FP.NmKeep{}:
          locked_names(ss, t, rest, e)
        case FP.NmStop{_why}:
          locked_names(ss, t, rest, e)

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
            FP.names.lay(FP.name.parts.of(F.sects(w), w), FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w)))),
            FP.outcome.then(FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
              FP.names.outcome(FP.name.parts.of(F.sects(w), w))),
            locked_names(F.sects(w), FP.name.parts.of(F.sects(w), w),
              FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
              locked_all(F.sects(w), F.replies(w), F.here(w), L.lock.hub(F.sects(w)),
                L.hashes(F.sects(w)))))

def Laws.fetch_lays_the_lock(w):
  locked_led(F.ledger(w), F.lock(w), w)

# ---------------------------------------------------------------------------
# the checkout around a git package

# LAW: a sealed plan's effects are the ones it was given, or none
law weighed_seal:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {FP.lays.weighed(ss, rs, here, es) == True{} : Bool}
  {FP.lays.weighed(ss, rs, here, FP.effects(FP.seal(es, o))) == True{} : Bool}

def weighed_seal(_ss, _rs, _here, _es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

# LAW: files that weighed, laid when they pass `good`, are laid for a
# package whose checkout weighed
law weighed_good:
  for b: Bool
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +fs: List<&2, K.Item>
  for +h: String
  for +ls: List<&2, W.Source>
  for rest: List<&2, P.Effect>
  for q: {String.is_empty(FP.weighed(ss, rs, here, h)) == True{} : Bool}
  for e: {FP.lays.weighed(ss, rs, here, rest) == True{} : Bool}
  {FP.lays.weighed(ss, rs, here, FP.effect.v(FP.judge.got(b, fs, h, ls), rest)) == True{}
    : Bool}

def weighed_good(b, ss, rs, here, _fs, h, _ls, rest, q, e):
  match b:
    case False{}:
      e
    case True{}:
      %Equal.sym(Bool, String.is_empty(FP.weighed(ss, rs, here, h)), True{}, q)
        : {Bool.and(_, FP.lays.weighed(ss, rs, here, rest)) == True{} : Bool}
      e

# LAW: files that arrived, judged once the checkout's weighing is known
law weighed_got:
  for k: Bool
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +fs: List<&2, K.Item>
  for +h: String
  for +ls: List<&2, W.Source>
  for rest: List<&2, P.Effect>
  for q: {String.is_empty(FP.weighed(ss, rs, here, h)) == k : Bool}
  for e: {FP.lays.weighed(ss, rs, here, rest) == True{} : Bool}
  {FP.lays.weighed(ss, rs, here,
    FP.effect.v(FP.judge(fs, h, FP.weigh.got(k, FP.weighed(ss, rs, here, h), ls)), rest))
    == True{} : Bool}

def weighed_got(k, ss, rs, here, fs, h, ls, rest, q, e):
  match k:
    case False{}:
      e
    case True{}:
      weighed_good(FP.good(fs, h, ls), ss, rs, here, fs, h, ls, rest, q, e)

# LAW: so does every verdict on a package of the lock, wherever it stands
law weighed_one:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +fs: List<&2, K.Item>
  for +h: String
  for p: FP.Part
  for rest: List<&2, P.Effect>
  for e: {FP.lays.weighed(ss, rs, here, rest) == True{} : Bool}
  {FP.lays.weighed(ss, rs, here,
    FP.effect.v(FP.judge(fs, h, FP.weigh.part(FP.weighed(ss, rs, here, h), p)), rest))
    == True{} : Bool}

def weighed_one(ss, rs, here, fs, h, p, rest, e):
  match p:
    case FP.AskLaid{}:
      e
    case FP.AskFetch{}:
      e
    case FP.Have{}:
      e
    case FP.Got{+ls}:
      weighed_got(String.is_empty(FP.weighed(ss, rs, here, h)), ss, rs, here, fs, h, ls,
        rest, {==}, e)
    case FP.No{_why}:
      e

# LAW: and so do the verdicts on every package of the lock
law weighed_all:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +hub: String
  for hs: List<&2, String>
  {FP.lays.weighed(ss, rs, here, FP.effects.of(FP.judged(FP.parts(ss, rs, here, hub, hs))))
    == True{} : Bool}

def weighed_all(ss, rs, here, hub, hs):
  match hs:
    case []:
      {==}
    case +h <> +t:
      weighed_one(ss, rs, here, FP.locked(ss, h), h,
        FP.part(rs, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), here, hub, h),
        FP.effects.of(FP.judged(FP.parts(ss, rs, here, hub, t))),
        weighed_all(ss, rs, here, hub, t))

# LAW: one names file, in front of trees whose checkouts weighed right
law weighed_put:
  for b: Bool
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +nv: String
  for +hash: String
  for was: String
  for +rest: List<&2, P.Effect>
  for e: {FP.lays.weighed(ss, rs, here, rest) == True{} : Bool}
  {FP.lays.weighed(ss, rs, here, FP.name.put.at(b, nv, hash, was, rest)) == True{} : Bool}

def weighed_put(b, _ss, _rs, _here, _nv, _hash, _was, _rest, e):
  match b:
    case True{}:
      e
    case False{}:
      e

# LAW: every names file, so
law weighed_names:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for ms: List<&2, FP.Nm>
  for +rest: List<&2, P.Effect>
  for e: {FP.lays.weighed(ss, rs, here, rest) == True{} : Bool}
  {FP.lays.weighed(ss, rs, here, FP.names.lay(ms, rest)) == True{} : Bool}

def weighed_names(ss, rs, here, ms, rest, e):
  match ms:
    case []:
      e
    case m <> +t:
      match m:
        case FP.NmPut{+nv, +hash, +was}:
          weighed_put(String.is_empty(was), ss, rs, here, nv, hash, was, FP.names.lay(t, rest),
            weighed_names(ss, rs, here, t, rest, e))
        case FP.NmAsk{_nv}:
          weighed_names(ss, rs, here, t, rest, e)
        case FP.NmKeep{}:
          weighed_names(ss, rs, here, t, rest, e)
        case FP.NmStop{_why}:
          weighed_names(ss, rs, here, t, rest, e)

law weighed_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  {FP.lays.weighed(F.sects(w), F.replies(w), F.here(w), FP.effects(FP.plan.led(b, g, w)))
    == True{} : Bool}

def weighed_led(b, g, w):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          weighed_seal(F.sects(w), F.replies(w), F.here(w),
            FP.names.lay(FP.name.parts.of(F.sects(w), w), FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w)))),
            FP.outcome.then(FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
              FP.names.outcome(FP.name.parts.of(F.sects(w), w))),
            weighed_names(F.sects(w), F.replies(w), F.here(w), FP.name.parts.of(F.sects(w), w),
              FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
              weighed_all(F.sects(w), F.replies(w), F.here(w), L.lock.hub(F.sects(w)),
                L.hashes(F.sects(w)))))

def Laws.fetch_lays_weighed(w):
  weighed_led(F.ledger(w), F.lock(w), w)

# LAW: the reason a weighing gives is empty exactly when the lock records a
# narHash and the checkout weighed to it
law nar_why_empty:
  for none: Bool
  for same: Bool
  for +h: String
  for +want: String
  for +got: String
  for +url: String
  for +rev: String
  {String.is_empty(FP.nar.why(none, same, h, want, got, url, rev))
    == Bool.and(Bool.not(none), same) : Bool}

def nar_why_empty(none, same, _h, _want, _got, _url, _rev):
  match none:
    case True{}:
      {==}
    case False{}:
      match same:
        case True{}:
          {==}
        case False{}:
          {==}

def Laws.fetch_weighs_the_checkout(ss, rs, here, h, url, rev, entry, root, nar, tag, got, fs, q, a):
  %Equal.sym(L.Src, L.pack.src(L.pack_of(ss, h)), L.Git{url, rev, entry, root, nar, tag}, q)
    : {String.is_empty(FP.weighed.src(_, rs, here, h))
      == Bool.and(Bool.not(String.is_empty(nar)), String.eq(got, nar)) : Bool}
  %Equal.sym(F.Heard, F.heard(rs, F.Git{h, Up.Clone{Path.anchor(here, url), rev}}),
    F.Heard{F.Said{Up.Cloned{got, fs}}}, a)
    : {String.is_empty(FP.weighed.heard(_, h, nar, url, rev))
      == Bool.and(Bool.not(String.is_empty(nar)), String.eq(got, nar)) : Bool}
  nar_why_empty(String.is_empty(nar), String.eq(got, nar), h, nar, got, url, rev)

# LAW: a reason that is not empty stops the package with it
law unweighed_stops:
  for k: Bool
  for +fs: List<&2, K.Item>
  for +h: String
  for +why: String
  for ls: List<&2, W.Source>
  for n: {k == False{} : Bool}
  {FP.judge(fs, h, FP.weigh.got(k, why, ls)) == FP.Stop{why} : FP.Verdict}

def unweighed_stops(k, _fs, _h, _why, _ls, n):
  match k:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {FP.judge(_fs, _h, FP.weigh.got(True{}, _why, _ls)) == FP.Stop{_why}
        : FP.Verdict}, n)

def Laws.fetch_refuses_unweighed(fs, h, why, ls, n):
  unweighed_stops(String.is_empty(why), fs, h, why, ls, n)
