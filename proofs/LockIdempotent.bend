# proofs of laws/LockIdempotent.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/ledger/ignore.bend as I
import ../src/ledger/upgrade.bend as U
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../laws/GitignoreAllowlistIsLedger.bend as L1
import ../laws/LockIdempotent.bend as Laws
import ../laws/LockReproducible.bend as L2
import ../laws/NarWhyAgrees.bend as L3
import ../laws/defs/LedgerReadsBackPremise.bend as D1
import ../laws/defs/LockInputs.bend as D2
import ../laws/defs/WorldAfterLock.bend as D3
import ./lemmas/AllowlistLines.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2
import ./lemmas/PlanEffectFacts.bend as M3

# Idempotence. A clone that passed weighed to the narHash the ledger records,
# so the same bytes read from BEND_LIB, which are judged as a clone weighed to
# that narHash (`lib_as_clone.src`), pass the same way. Every verdict is what
# it was, so the Inputs are, and `lock_reproducible` gives the rest.

# LAW: a weighed git package that passed was weighed with no reason to refuse
law weighed_passes:
  for why: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {D2.passed(W.git.weighed(why, hash, manifest, ss)) == True{} : Bool}
  {why == "" : String}

def weighed_passes(why, _hash, _manifest, _ss, e):
  match why:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Eq.bit.absurd(&2, {SCon{h, t} == "" : String}, e)

# LAW: a checkout whose NAR hash the ledger agreed with has a NAR hash the
# ledger records, so the ledger's own agrees with it too
law nar_agrees_when_passed:
  for +nar: String
  for +got: String
  for +url: String
  for +rev: String
  for e: {L.nar.why(nar, got, url, rev) == "" : String}
  {L.nar.why(nar, nar, url, rev) == "" : String}

def nar_agrees_when_passed(nar, got, url, rev, e):
  match nar:
    case SNil{}:
      Eq.bit.absurd(&2, {L.nar.why("", "", url, rev) == "" : String},
        Equal.cong(String, Bool, s => String.is_empty(s),
          L.nar.why("", got, url, rev), "", e))
    case SCon{+h, +t}:
      L3.nar_why_agrees(SCon{h, t}, url, rev, {==})

# LAW: a clone that passed is judged as the same bytes read from BEND_LIB
law clone_passed.src:
  for src: L.Src
  for +got: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {D2.passed(W.accept.src(src, W.Clone{got}, hash, manifest, ss)) == True{} : Bool}
  {W.accept.src(src, W.Lib{}, hash, manifest, ss)
    == W.accept.src(src, W.Clone{got}, hash, manifest, ss) : W.Verdict}

def clone_passed.src(src, got, hash, manifest, ss, e):
  match src:
    case L.Hub{}:
      Eq.bit.absurd(&2, {W.accept.src(L.Hub{}, W.Lib{}, hash, manifest, ss)
        == W.accept.src(L.Hub{}, W.Clone{got}, hash, manifest, ss) : W.Verdict}, e)
    case L.Git{+url, +rev, _entry, _root, +nar, _tag}:
      +same = weighed_passes(L.nar.why(nar, got, url, rev), hash, manifest, ss, e)
      Equal.trans(W.Verdict,
        W.git.weighed(L.nar.why(nar, nar, url, rev), hash, manifest, ss),
        W.git.weighed("", hash, manifest, ss),
        W.git.weighed(L.nar.why(nar, got, url, rev), hash, manifest, ss),
        Equal.cong(String, W.Verdict, why => W.git.weighed(why, hash, manifest, ss),
          L.nar.why(nar, nar, url, rev), "",
          nar_agrees_when_passed(nar, got, url, rev, same)),
        Equal.sym(W.Verdict,
          W.git.weighed(L.nar.why(nar, got, url, rev), hash, manifest, ss),
          W.git.weighed("", hash, manifest, ss),
          Equal.cong(String, W.Verdict, why => W.git.weighed(why, hash, manifest, ss),
            L.nar.why(nar, got, url, rev), "", same)))
    case L.Member{_path, _entry}:
      {==}

# LAW: a cloned tree, laid when it passed, is judged as it was
law after.clone_judged:
  for b: Bool
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for +got: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {D2.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})) == b
    : Bool}
  {W.accept(orgs, hub, hash, D3.after.clone(b, got, manifest, ss))
    == W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss}) : W.Verdict}

def after.clone_judged(b, orgs, _hub, hash, got, manifest, ss, e):
  match b:
    case True{}:
      clone_passed.src(L.origin(orgs, hash), got, hash, manifest, ss, e)
    case False{}:
      {==}

# LAW: one answer, as the next lock reads it, is judged as it was
law after.one_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {W.accept(orgs, hub, hash, D3.after.one(orgs, hub, hash, a))
    == W.accept(orgs, hub, hash, a) : W.Verdict}

def after.one_judged(orgs, hub, hash, a):
  match a:
    case W.Miss{_why}:
      {==}
    case W.Said{_text}:
      {==}
    case W.Locked{_text}:
      {==}
    case W.Got{how, +manifest, +ss}:
      match how:
        case W.Lib{}:
          {==}
        case W.Clone{+got}:
          after.clone_judged(
            D2.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
            orgs, hub, hash, got, manifest, ss, {==})
        case W.Served{}:
          {==}

# LAW: every answer, as the next lock reads it, is judged as it was
law after_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {W.judge(orgs, hub, D3.after.all(orgs, hub, rs)) == W.judge(orgs, hub, rs)
    : List<&2, W.Judged>}

def after_judged(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+ask, a} <> t:
      Equal.trans(List<&2, W.Judged>,
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask),
          D3.after.one(orgs, hub, W.ask.hash(ask), a))}
          <> W.judge(orgs, hub, D3.after.all(orgs, hub, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, D3.after.all(orgs, hub, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, t),
        Equal.cong(W.Verdict, List<&2, W.Judged>,
          v => W.Judged{W.ask.hash(ask), v}
            <> W.judge(orgs, hub, D3.after.all(orgs, hub, t)),
          W.accept(orgs, hub, W.ask.hash(ask),
            D3.after.one(orgs, hub, W.ask.hash(ask), a)),
          W.accept(orgs, hub, W.ask.hash(ask), a),
          after.one_judged(orgs, hub, W.ask.hash(ask), a)),
        Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
          js => W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)} <> js,
          W.judge(orgs, hub, D3.after.all(orgs, hub, t)),
          W.judge(orgs, hub, t),
          after_judged(orgs, hub, t)))

# LAW: the World a lock that succeeded leaves has the Inputs it read
law after.laid_inputs:
  for w: W.World
  {W.inputs(D3.after.laid(w)) == W.inputs(w) : W.Inputs}

def after.laid_inputs(w):
  match w:
    case W.World{+args, +ledger, listing, replies, +ups}:
      Equal.cong(List<&2, W.Judged>, W.Inputs,
        js => W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          List.append(&2, W.Judged,
            W.judge(W.next.origins(W.next(args, ledger, ups)),
              W.next.hub(W.next(args, ledger, ups)),
              W.laid.replies(Up.next.trees(W.next(args, ledger, ups)),
                W.next.origins(W.next(args, ledger, ups)),
                W.next.hub(W.next(args, ledger, ups)))), js)},
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)),
          D3.after.all(W.next.origins(W.next(args, ledger, ups)),
            W.next.hub(W.next(args, ledger, ups)), replies)),
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies),
        after_judged(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies))

# LAW: whether or not the lock refused, the World it leaves writes its lock
law after.pick_put:
  for b: Bool
  for +w: W.World
  {P.put(D3.after.pick(b, w), "ez.lock.toml") == P.put(w, "ez.lock.toml")
    : P.Wrote}

def after.pick_put(b, w):
  match b:
    case True{}:
      {==}
    case False{}:
      L2.lock_reproducible(D3.after.laid(w), w, after.laid_inputs(w))

# A plain World's args say no `--upgrade`, and it leaves what a plain lock
# leaves; the other arm contradicts the premise.
def Laws.lock_idempotent(w, e):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.put(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing,
                replies, ups}), "ez.lock.toml") == P.put(W.World{W.Args{True{}, only, here}, ledger,
                listing, replies, ups}, "ez.lock.toml") : P.Wrote}, e)
            case False{}:
              after.pick_put(P.refuses(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups}),
                W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups})

# LAW: a cloned tree, as the next lock reads it, is not one it lays: laid, it
# is read from BEND_LIB, and not laid, it failed
law fresh.clone:
  for b: Bool
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for +got: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {D2.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})) == b
    : Bool}
  {Laws.fresh.one(orgs, hub, hash, D3.after.clone(b, got, manifest, ss)) == []
    : List<&2, String>}

def fresh.clone(b, orgs, hub, hash, got, manifest, ss, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, List<&2, String>,
        x => Bool.pick(List<&2, String>, x, [hash], []),
        D2.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
        False{}, e)

# LAW: no answer, as the next lock reads it, is a tree it lays
law fresh.one_after:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {Laws.fresh.one(orgs, hub, hash, D3.after.one(orgs, hub, hash, a)) == []
    : List<&2, String>}

def fresh.one_after(orgs, hub, hash, a):
  match a:
    case W.Miss{_why}:
      {==}
    case W.Said{_text}:
      {==}
    case W.Locked{_text}:
      {==}
    case W.Got{how, +manifest, +ss}:
      match how:
        case W.Lib{}:
          {==}
        case W.Clone{+got}:
          fresh.clone(
            D2.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
            orgs, hub, hash, got, manifest, ss, {==})
        case W.Served{}:
          {==}

# LAW: and none of them is
law fresh.all_after:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {Laws.fresh.all(orgs, hub, D3.after.all(orgs, hub, rs)) == [] : List<&2, String>}

def fresh.all_after(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+ask, a} <> t:
      Equal.trans(List<&2, String>,
        List.append(&2, String,
          Laws.fresh.one(orgs, hub, W.ask.hash(ask),
            D3.after.one(orgs, hub, W.ask.hash(ask), a)),
          Laws.fresh.all(orgs, hub, D3.after.all(orgs, hub, t))),
        Laws.fresh.all(orgs, hub, D3.after.all(orgs, hub, t)),
        [],
        Equal.cong(List<&2, String>, List<&2, String>,
          x => List.append(&2, String, x,
            Laws.fresh.all(orgs, hub, D3.after.all(orgs, hub, t))),
          Laws.fresh.one(orgs, hub, W.ask.hash(ask),
            D3.after.one(orgs, hub, W.ask.hash(ask), a)),
          [],
          fresh.one_after(orgs, hub, W.ask.hash(ask), a)),
        fresh.all_after(orgs, hub, t))

# LAW: the World a lock that succeeded leaves has no tree for the next to lay
law fresh.laid:
  for w: W.World
  {Laws.fresh.origins(D3.after.laid(w)) == [] : List<&2, String>}

def fresh.laid(w):
  match w:
    case W.World{+args, +ledger, _listing, replies, +ups}:
      fresh.all_after(W.next.origins(W.next(args, ledger, ups)),
        W.next.hub(W.next(args, ledger, ups)), replies)

# LAW: a plain lock that succeeded leaves no tree for the next to lay
law relock.plain:
  for +w: W.World
  for ok: {P.refuses(w) == False{} : Bool}
  {Laws.fresh.origins(D3.after.pick(P.refuses(w), w)) == [] : List<&2, String>}

def relock.plain(w, ok):
  Equal.trans(List<&2, String>,
    Laws.fresh.origins(D3.after.pick(P.refuses(w), w)),
    Laws.fresh.origins(D3.after.pick(False{}, w)),
    [],
    Equal.cong(Bool, List<&2, String>, b => Laws.fresh.origins(D3.after.pick(b, w)),
      P.refuses(w), False{}, ok),
    fresh.laid(w))

def Laws.relock_lays_nothing(w, e, ok):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {Laws.fresh.origins(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing,
                replies, ups})) == [] : List<&2, String>}, e)
            case False{}:
              relock.plain(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups}, ok)

# The `.gitignore` the first upgrade left is in sync with the ledger it left,
# so the second writes none: it is the file it read, which the first found in
# sync, or the file `I.sync` made, which `I.sync` leaves as it is
# (`Laws.sync_idempotent`), for a ledger whose vendored hashes hold no newline.

# whether the `.gitignore` an upgrade of a ledger model writes, given the one
# it reads, is no write at all, for a ledger whose vendored hashes hold no
# newline
def gi.ok(+model: M.Read, +g: String) -> Bool:
  +ds = D2.ledger.deps(model)
  Bool.or(Bool.not(Str.clear.all(I.vended(ds), '\n')), List.is_empty(&2, Up.Edit, M3.gi.of(model, g)))

# LAW: the file `I.sync` made is in sync, when no vendored hash holds a newline
law g.sync.cv:
  for cv: Bool
  for +dds: List<&2, M.Dep>
  for +ig: String
  for +ecv: {Str.clear.all(I.vended(dds), '\n') == cv : Bool}
  {Bool.or(Bool.not(cv),
    List.is_empty(&2, Up.Edit, Up.edit.if(String.eq(I.sync(dds, I.sync(dds, ig)), I.sync(dds, ig)),
      ".gitignore", I.sync(dds, I.sync(dds, ig)), []))) == True{} : Bool}

def g.sync.cv(cv, dds, ig, ecv):
  match cv:
    case False{}:
      {==}
    case True{}:
      si = Equal.sym(String, I.sync(dds, I.sync(dds, ig)), I.sync(dds, ig), L1.sync_idempotent(dds, ig, ecv))
      %si : {Bool.or(False{}, List.is_empty(&2, Up.Edit, Up.edit.if(String.eq(_, I.sync(dds, ig)),
        ".gitignore", _, []))) == True{} : Bool}
      ns = Equal.sym(Bool, String.eq(I.sync(dds, ig), I.sync(dds, ig)), True{}, Eq.string_eq_self(I.sync(dds, ig)))
      %ns : {Bool.or(False{}, List.is_empty(&2, Up.Edit, Up.edit.if(_, ".gitignore", I.sync(dds, ig), [])))
        == True{} : Bool}
      {==}

# LAW: the allowlist of the file `I.sync` made, or of one it found in sync, is
# in sync
law g.sync.b:
  for b: Bool
  for +dds: List<&2, M.Dep>
  for +ig: String
  for eb: {String.eq(I.sync(dds, ig), ig) == b : Bool}
  {Bool.or(Bool.not(Str.clear.all(I.vended(dds), '\n')),
    List.is_empty(&2, Up.Edit, Up.edit.if(
      String.eq(I.sync(dds, D3.ig.left(Up.edit.if(b, ".gitignore", I.sync(dds, ig), []), ig)),
        D3.ig.left(Up.edit.if(b, ".gitignore", I.sync(dds, ig), []), ig)), ".gitignore",
      I.sync(dds, D3.ig.left(Up.edit.if(b, ".gitignore", I.sync(dds, ig), []), ig)), [])))
    == True{} : Bool}

def g.sync.b(b, dds, ig, eb):
  match b:
    case True{}:
      neb = Equal.sym(Bool, String.eq(I.sync(dds, ig), ig), True{}, eb)
      %neb : {Bool.or(Bool.not(Str.clear.all(I.vended(dds), '\n')),
        List.is_empty(&2, Up.Edit, Up.edit.if(_, ".gitignore", I.sync(dds, ig), []))) == True{} : Bool}
      M2.mv.or_r(Bool.not(Str.clear.all(I.vended(dds), '\n')), True{}, {==})
    case False{}:
      g.sync.cv(Str.clear.all(I.vended(dds), '\n'), dds, ig, {==})

# LAW: whether a pin moved: the ledger it leaves vendors the hashes the
# allowlist was synced with
law g.done:
  for dm: Bool
  for tm: Bool
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for +ig: String
  for +fs: List<&2, Up.Found>
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  {gi.ok(Up.next.model(Up.done(M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm, dsy,
    dtr, [], ""},
    Up.Tools{tts, tm, tsy, [], ""}, ig, fs)), D3.ig.left(Up.next.edits(Up.done(M.Manifest{name, entry, bin, hub,
      hubpa, hubpv, ds,
      ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig, fs)), ig)) == True{} : Bool}

def g.done(dm, tm, name, entry, bin, hub, hubpa, hubpv, _ds, ts, dds, _ss, _es, _dsy, _dtr, _tts, _tsy, ig, _fs, hq):
  match dm:
    case True{}:
      g.sync.b(String.eq(I.sync(dds, ig), ig), dds, ig, {==})
    case False{}:
      match tm:
        case True{}:
          g.sync.b(String.eq(I.sync(dds, ig), ig), dds, ig, {==})
        case False{}:
          %hq : {gi.ok(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, _, ts}},
            D3.ig.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []), ig))
            == True{} : Bool}
          g.sync.b(String.eq(I.sync(dds, ig), ig), dds, ig, {==})

# LAW: the sources, once they are known
law g.srcs:
  for srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for +ig: String
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss,
      es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es,
    dm, dsy, dtr,
    [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)), D3.ig.left(Up.next.edits(Up.got.srcs(srcs, M.Manifest{name,
      entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [],
        ""}, ig)),
        ig)) == True{} : Bool}

def g.srcs(srcs, dm, tm, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, hq, se):
  match srcs:
    case Up.Srcs{fs}:
      g.done(dm, tm, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, fs, hq)
    case Up.SrcsWait{ask}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, hubpa,
        hubpv, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)),
          D3.ig.left(Up.next.edits(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
            ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)), ig)) == True{} : Bool},
              se)
    case Up.SrcsNo{+why}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, hubpa,
        hubpv, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)),
          D3.ig.left(Up.next.edits(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
            ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)), ig)) == True{} : Bool},
              M2.mv.halt_clash(why, se))

# LAW: `.gitignore`, once it is known
law g.ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
    ts},
      Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds,
    ss, es, dm,
    dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})), D3.ig.left(Up.next.edits(Up.got.ignore(said, srcs,
      M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""},
        Up.Tools{tts, tm, tsy,
        [], ""})), D3.ig.said(said))) == True{} : Bool}

def g.ignore(said, srcs, dm, tm, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, hq, se):
  match said:
    case Up.Said{+ig}:
      g.srcs(srcs, dm, tm, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, hq, se)
    case Up.Unsaid{+why}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub,
        hubpa, hubpv, ds,
        ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
          D3.ig.left(Up.next.edits(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, hubpa,
            hubpv, ds, ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
              D3.ig.said(Up.Unsaid{why}))) == True{} : Bool}, M2.mv.halt_clash(why, se))
    case Up.Unasked{ask}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub,
        hubpa, hubpv,
        ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
          D3.ig.left(Up.next.edits(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub, hubpa,
            hubpv, ds, ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
              D3.ig.said(Up.Unasked{ask}))) == True{} : Bool}, se)

# LAW: the walks, once they are done or refused
law g.pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for hq: {M2.dstay(dd, ds) == ds : List<&2, M.Dep>}
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
      ts}))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
    D3.ig.left(Up.next.edits(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
      D3.ig.read(rs))) == True{} : Bool}

def g.pins(dd, tt, rs, name, entry, bin, hub, hubpa, hubpv, ds, ts, hq, se):
  match dd tt:
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}} Up.Tools{tts, tm, tsy, tasks, tbad}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}},
        Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
          D3.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}}, Up.Tools{tts, tm,
            tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
              D3.ig.read(rs))) == True{} : Bool},
              se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}} Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}}, Up.Tools{tts,
        tm, tsy, tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
          D3.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}}, Up.Tools{tts, tm, tsy,
            tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
              D3.ig.read(rs))) == True{} : Bool}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}} Up.Tools{tts, tm, tsy, tasks, SNil{}}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}},
        Up.Tools{tts, tm, tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
          D3.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}}, Up.Tools{tts, tm,
            tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
              D3.ig.read(rs))) == True{} : Bool}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}} Up.Tools{tts, tm, tsy, a <> as, SNil{}}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}}, Up.Tools{tts, tm,
        tsy, a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
          D3.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}}, Up.Tools{tts, tm, tsy,
            a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
              D3.ig.read(rs))) == True{} : Bool}, se)
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      g.ignore(Up.text.said(rs, Up.Ignore{}), Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), dm, tm,
        name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, hq, se)

# LAW: once `--package` is known to name something
law g.known:
  for k: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
      ts}))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
    D3.ig.left(Up.next.edits(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})),
      D3.ig.read(rs))) == True{} : Bool}

def g.known(k, rs, only, name, entry, bin, hub, hubpa, hubpv, ds, ts, se):
  match k:
    case False{}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, hubpa,
        hubpv, ds, ts})),
        D3.ig.left(Up.next.edits(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
          ts})),
          D3.ig.read(rs))) == True{} : Bool}, M2.mv.halt_clash("ez: no dependency or tool named " ++ only, se))
    case True{}:
      g.pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), rs, name, entry, bin, hub, hubpa,
        hubpv,
        ds, ts, M2.dq.all(rs, only, M.hub.or(hub), ds), se)

# LAW: an upgrade that does not stop leaves a `.gitignore` in sync with the
# ledger it leaves, for a ledger whose vendored hashes hold no newline
law g.top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.next(only, r, rs)), D3.ig.left(Up.next.edits(Up.next(only, r, rs)),
    D3.ig.read(rs))) == True{} : Bool}

def g.top(r, only, rs, se):
  match r:
    case M.Bad{why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +hubpa, +hubpv, +ds, +ts}:
          g.known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), rs, only, name, entry, bin, hub, hubpa, hubpv,
            ds, ts,
            se)

# ---------------------------------------------------------------------------
# the plan of the second upgrade

# LAW: a decision and its view agree on everything but what they say
law view_model:
  for nx: Up.Next
  {Up.next.model(M2.view(nx)) == Up.next.model(nx) : M.Read}

def view_model(nx):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, vs, sy, ed, fd, dr, sw}:
      {==}

law view_read:
  for nx: Up.Next
  {Up.next.read(M2.view(nx)) == Up.next.read(nx) : M.Read}

def view_read(nx):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, vs, sy, ed, fd, dr, sw}:
      {==}

# LAW: what the lock may depend on is the same through the view
law view_inputs:
  for nx: Up.Next
  for listing: W.Listing
  for replies: List<&2, W.Reply>
  {W.inputs.of(M2.view(nx), listing, replies) == W.inputs.of(nx, listing, replies) : W.Inputs}

def view_inputs(nx, _listing, _replies):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, vs, sy, ed, fd, dr, sw}:
      {==}

# LAW: and so is every path a plan leaves: what a person is told writes none
law view_put:
  for nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for +p: String
  {P.put.plan(P.made(M2.view(nx), cs, js, d), p) == P.put.plan(P.made(nx, cs, js, d), p) : P.Wrote}

def view_put(nx, cs, js, d, p):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, +vs, sy, +ed, +fd, +dr, +sw}:
      match d:
        case P.Doc{+text}:
          Equal.sym(P.Wrote,
            P.put.in(P.says.of(sy, P.lays(cs, vs, js, P.names.lay(L.names.read(text),
              P.edits.of(ed, P.edits.of(Up.edit.sources(fd, sw),
                P.drops.of(dr, [P.Write{P.lockfile(), text}])))))), p),
            P.put.in(P.lays(cs, vs, js, P.names.lay(L.names.read(text),
              P.edits.of(ed, P.edits.of(Up.edit.sources(fd, sw),
                P.drops.of(dr, [P.Write{P.lockfile(), text}]))))), p),
            M3.says_put(sy, P.lays(cs, vs, js, P.names.lay(L.names.read(text),
              P.edits.of(ed, P.edits.of(Up.edit.sources(fd, sw),
                P.drops.of(dr, [P.Write{P.lockfile(), text}]))))), p))
        case P.Stop{_why}:
          {==}

# LAW: judging a list of answers is judging each part
law judge_append:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for xs: List<&2, W.Reply>
  for +ys: List<&2, W.Reply>
  {W.judge(orgs, hub, List.append(&2, W.Reply, xs, ys))
    == List.append(&2, W.Judged, W.judge(orgs, hub, xs), W.judge(orgs, hub, ys)) : List<&2, W.Judged>}

def judge_append(orgs, hub, xs, ys):
  match xs:
    case []:
      {==}
    case W.Reply{+ask, +a} <> t:
      Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
        js => W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)} <> js,
        W.judge(orgs, hub, List.append(&2, W.Reply, t, ys)),
        List.append(&2, W.Judged, W.judge(orgs, hub, t), W.judge(orgs, hub, ys)),
        judge_append(orgs, hub, t, ys))

# LAW: a string that is empty is ""
law empty_nil:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {s == "" : String}

def empty_nil(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Eq.bit.absurd(&2, {SCon{h, t} == "" : String}, e)

# LAW: a list that is empty is []
law edits_nil:
  for es: List<&2, Up.Edit>
  for e: {List.is_empty(&2, Up.Edit, es) == True{} : Bool}
  {es == [] : List<&2, Up.Edit>}

def edits_nil(es, e):
  match es:
    case []:
      {==}
    case h <> t:
      Eq.bit.absurd(&2, {h <> t == [] : List<&2, Up.Edit>}, e)

# LAW: the target's inputs, with every tree read from BEND_LIB, are the first
# run's
law after_inputs.rest:
  for +nx1: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for es: {Up.next.stop(nx1) == "" : String}
  {W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing),
    W.judge(W.next.origins(nx1), W.next.hub(nx1),
      D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies)))}
    == W.inputs.of(nx1, listing, replies) : W.Inputs}

def after_inputs.rest(nx1, listing, replies, es):
  +o = W.next.origins(nx1)
  +h = W.next.hub(nx1)
  +laid = W.laid.replies(Up.next.trees(nx1), o, h)
  Equal.trans(W.Inputs,
    W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing),
      W.judge(o, h, D3.after.all(o, h, List.append(&2, W.Reply, laid, replies)))},
    W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing),
      List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies))},
    W.inputs.of(nx1, listing, replies),
    Equal.cong(List<&2, W.Judged>, W.Inputs,
      js => W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing), js},
      W.judge(o, h, D3.after.all(o, h, List.append(&2, W.Reply, laid, replies))),
      List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies)),
      Equal.trans(List<&2, W.Judged>,
        W.judge(o, h, D3.after.all(o, h, List.append(&2, W.Reply, laid, replies))),
        W.judge(o, h, List.append(&2, W.Reply, laid, replies)),
        List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies)),
        after_judged(o, h, List.append(&2, W.Reply, laid, replies)),
        judge_append(o, h, laid, replies))),
    Equal.cong(String, W.Inputs,
      s => W.Inputs{Up.next.read(nx1), s, W.listing.of(nx1, listing),
        List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies))},
      "", Up.next.stop(nx1), Equal.sym(String, Up.next.stop(nx1), "", es)))

# LAW: the second upgrade's lock reads what the first one's did: the ledger
# the first wrote, read, which it decided the target on, no refusal, the
# sources as the first left them, and every tree it read, now from BEND_LIB
law after_inputs:
  for +nx1: Up.Next
  for nx2: Up.Next
  for +g: String
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for e2: {M2.view(nx2) == M3.target(Up.next.read(nx1), g) : Up.Next}
  for es: {Up.next.stop(nx1) == "" : String}
  {W.inputs.of(nx2, W.listing.of(nx1, listing),
    D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies)))
    == W.inputs.of(nx1, listing, replies) : W.Inputs}

def after_inputs(nx1, nx2, g, listing, replies, e2, es):
  Equal.trans(W.Inputs,
    W.inputs.of(nx2, W.listing.of(nx1, listing),
      D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
    W.inputs.of(M3.target(Up.next.read(nx1), g), W.listing.of(nx1, listing),
      D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
    W.inputs.of(nx1, listing, replies),
    Equal.trans(W.Inputs,
      W.inputs.of(nx2, W.listing.of(nx1, listing),
        D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
      W.inputs.of(M2.view(nx2), W.listing.of(nx1, listing),
        D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
      W.inputs.of(M3.target(Up.next.read(nx1), g), W.listing.of(nx1, listing),
        D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
      Equal.sym(W.Inputs,
        W.inputs.of(M2.view(nx2), W.listing.of(nx1, listing),
          D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
        W.inputs.of(nx2, W.listing.of(nx1, listing),
          D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
        view_inputs(nx2, W.listing.of(nx1, listing),
          D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies)))),
      Equal.cong(Up.Next, W.Inputs,
        x => W.inputs.of(x, W.listing.of(nx1, listing),
          D3.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
        M2.view(nx2), M3.target(Up.next.read(nx1), g), e2)),
    after_inputs.rest(nx1, listing, replies, es))

# LAW: a `.gitignore` write leaves every other path as it was
law gi_put.one:
  for +s: String
  for +p: String
  for wr: P.Wrote
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  {P.put.one(P.Write{".gitignore", s}, p, wr) == wr : P.Wrote}

def gi_put.one(s, p, wr, ng):
  match wr:
    case P.Kept{}:
      nng = Equal.sym(Bool, String.eq(".gitignore", p), False{}, ng)
      %nng : {Bool.pick(P.Wrote, _, P.Put{s}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}
    case P.Put{l}:
      {==}

law gi_put.b:
  for b: Bool
  for +s: String
  for +rest: List<&2, P.Effect>
  for +p: String
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  {P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", s, []), rest), p) == P.put.in(rest, p) : P.Wrote}

def gi_put.b(b, s, rest, p, ng):
  match b:
    case True{}:
      {==}
    case False{}:
      gi_put.one(s, p, P.put.in(rest, p), ng)

# LAW: so does the `.gitignore` an upgrade of a model writes
law gi_put:
  for md: M.Read
  for +g: String
  for +rest: List<&2, P.Effect>
  for +p: String
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  {P.put.in(P.edits.of(M3.gi.of(md, g), rest), p) == P.put.in(rest, p) : P.Wrote}

def gi_put(md, g, rest, p, ng):
  match md:
    case M.Bad{_why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{_n, _e, _b, _h, _hpa, _hpv, +ds, _ts}:
          gi_put.b(String.eq(I.sync(ds, g), g), I.sync(ds, g), rest, p, ng)

# LAW: the lock's write leaves every other path as it was
law lock_put:
  for +text: String
  for +p: String
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.in([P.Write{P.lockfile(), text}], p) == P.Kept{} : P.Wrote}

def lock_put(text, p, nl):
  nnl = Equal.sym(Bool, String.eq("ez.lock.toml", p), False{}, nl)
  %nnl : {Bool.pick(P.Wrote, _, P.Put{text}, P.Kept{}) == P.Kept{} : P.Wrote}
  {==}

# LAW: the target's plan writes no path but the lock and `.gitignore`
law target_put:
  for +md: M.Read
  for +g: String
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for +p: String
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.made(M3.target(md, g), cs, js, d), p) == P.Kept{} : P.Wrote}

def target_put(md, g, cs, js, d, p, ng, nl):
  match d:
    case P.Doc{+text}:
      Equal.trans(P.Wrote,
        P.put.in(P.lays(cs, M3.vends.of(md), js,
          P.names.lay(L.names.read(text), P.edits.of(M3.gi.of(md, g), [P.Write{P.lockfile(), text}]))), p),
        P.put.in(P.edits.of(M3.gi.of(md, g), [P.Write{P.lockfile(), text}]), p),
        P.Kept{},
        M3.lays_names_put(cs, M3.vends.of(md), js, L.names.read(text),
          P.edits.of(M3.gi.of(md, g), [P.Write{P.lockfile(), text}]), p),
        Equal.trans(P.Wrote,
          P.put.in(P.edits.of(M3.gi.of(md, g), [P.Write{P.lockfile(), text}]), p),
          P.put.in([P.Write{P.lockfile(), text}], p),
          P.Kept{},
          gi_put(md, g, [P.Write{P.lockfile(), text}], p, ng),
          lock_put(text, p, nl)))
    case P.Stop{_why}:
      {==}

# LAW: and when it writes no `.gitignore`, no path but the lock
law target_put.clean:
  for +md: M.Read
  for +g: String
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for +p: String
  for eg: {M3.gi.of(md, g) == [] : List<&2, Up.Edit>}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.made(M3.target(md, g), cs, js, d), p) == P.Kept{} : P.Wrote}

def target_put.clean(md, g, cs, js, d, p, eg, nl):
  match d:
    case P.Doc{+text}:
      neg = Equal.sym(List<&2, Up.Edit>, M3.gi.of(md, g), [], eg)
      %neg : {P.put.plan(P.made(Up.Next{md, md, "", [], [], M3.vends.of(md), [], _, [], [], []}, cs, js, P.Doc{text}),
          p)
        == P.Kept{} : P.Wrote}
      Equal.trans(P.Wrote,
        P.put.in(P.lays(cs, M3.vends.of(md), js, P.names.lay(L.names.read(text), [P.Write{P.lockfile(), text}])), p),
        P.put.in([P.Write{P.lockfile(), text}], p),
        P.Kept{},
        M3.lays_names_put(cs, M3.vends.of(md), js, L.names.read(text), [P.Write{P.lockfile(), text}], p),
        lock_put(text, p, nl))
    case P.Stop{_why}:
      {==}

def core.fst(q: Up.Next & M.Read) -> Up.Next:
  (a, _b) = q
  a

def core.snd(q: Up.Next & M.Read) -> M.Read:
  (_a, b) = q
  b

# ---------------------------------------------------------------------------
# `ez lock --upgrade`, run again (laws/LockIdempotent.bend)

# LAW: an upgrade that does not refuse leaves the World `after.up.laid` says
law u.after:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  {D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
    ups}) == D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : W.World}

def u.after(only, here, ledger, listing, replies, ups, ok):
  nok = Equal.sym(Bool, P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}), False{}, ok)
  %nok : {D3.after.up.pick(_, W.World{W.Args{True{}, only, here}, ledger, listing, replies,
    ups}) == D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : W.World}
  {==}

# LAW: the ledger it wrote reads back as the model it rendered
law u.rb:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
  {W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
    ledger)) == Up.next.model(Up.next(only, W.parsed(ledger), ups)) : M.Read}

def u.rb(only, here, ledger, listing, replies, ups, ok, rb):
  Equal.trans(M.Read, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
    W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}))),
      Up.next.model(Up.next(only, W.parsed(ledger), ups)),
    Equal.cong(W.World, M.Read, x => W.parsed(W.ledger.of(x)), D3.after.up.laid(W.World{W.Args{True{}, only, here},
      ledger, listing, replies, ups}), D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
      Equal.sym(W.World, D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
        D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}), u.after(only,
          here, ledger,
          listing, replies, ups, ok))),
    rb)

# LAW: it did not stop
law u.se:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  {String.is_empty(Up.next.stop(Up.next(only, W.parsed(ledger), ups))) == True{} : Bool}

def u.se(only, _here, ledger, listing, replies, ups, ok):
  M3.mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok)

# The ledger an upgrade that does not stop writes reads back as the model it
# renders (laws/WrittenLedgerReadsBack.bend): `Up.done` stops (`Up.fit.why`)
# when a pin moved and the model is not renderable, and a renderable model
# reads back (`Laws.ledger_reads_back`). Every other arm reads the ledger it
# was given and renders it as it is.

# LAW: a renderable model, with whether it is given, reads back
law rm.ren:
  for f: Bool
  for +next: M.Manifest
  for ef: {Rend.renderable(next) == f : Bool}
  for se: {String.is_empty(Bool.pick(String, f, "", Rend.unrenderable())) == True{} : Bool}
  for rb: D1.ReadsBack()
  {M.parse(Rend.show(next)) == M.Good{next} : M.Read}

def rm.ren(f, next, ef, se, rb):
  match f:
    case True{}:
      rb(next, ef)
    case False{}:
      Eq.bit.absurd(&2, {M.parse(Rend.show(next)) == M.Good{next} : M.Read}, se)

# LAW: the ledger the lock is made from is the model, with whether a pin
# moved given
law rm.fit:
  for moved: Bool
  for +next: M.Manifest
  for old: M.Manifest
  for se: {String.is_empty(Up.fit.why(moved, next)) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.read.next(moved, Rend.show(next), old) == Up.model.next(moved, next, old) : M.Read}

def rm.fit(moved, next, _old, se, rb):
  match moved:
    case True{}:
      rm.ren(Rend.renderable(next), next, {==}, se, rb)
    case False{}:
      {==}

# LAW: so it is once every answer is in
law rm.done:
  for +old: M.Manifest
  for dd: Up.Deps
  for tt: Up.Tools
  for +ig: String
  for fs: List<&2, Up.Found>
  for se: {String.is_empty(Up.next.stop(Up.done(old, dd, tt, ig, fs))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.done(old, dd, tt, ig, fs)) == Up.next.model(Up.done(old, dd, tt, ig, fs)) : M.Read}

def rm.done(old, dd, tt, _ig, _fs, se, rb):
  match old dd tt:
    case M.Manifest{+n, +e, +b, +h, +hpa, +hpv, ods, ots} Up.Deps{+ds, _ss, _es, dm, _dsy, _dtr, _da, _db}
      Up.Tools{+ts, tm, _tsy, _ta, _tb}:
      rm.fit(Bool.or(dm, tm), M.Manifest{n, e, b, h, hpa, hpv, ds, ts},
        M.Manifest{n, e, b, h, hpa, hpv, ods, ots}, se, rb)

# LAW: and once the sources are asked for
law rm.srcs:
  for srcs: Up.Srcs
  for +old: M.Manifest
  for dd: Up.Deps
  for tt: Up.Tools
  for +ig: String
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, old, dd, tt, ig))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.got.srcs(srcs, old, dd, tt, ig)) == Up.next.model(Up.got.srcs(srcs, old, dd, tt, ig))
    : M.Read}

def rm.srcs(srcs, old, dd, tt, ig, se, rb):
  match srcs:
    case Up.Srcs{fs}:
      rm.done(old, dd, tt, ig, fs, se, rb)
    case Up.SrcsWait{_a}:
      {==}
    case Up.SrcsNo{_w}:
      {==}

# LAW: and once `.gitignore` is asked for
law rm.ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +old: M.Manifest
  for dd: Up.Deps
  for tt: Up.Tools
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs, old, dd, tt))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.got.ignore(said, srcs, old, dd, tt)) == Up.next.model(Up.got.ignore(said, srcs, old, dd, tt))
    : M.Read}

def rm.ignore(said, srcs, old, dd, tt, se, rb):
  match said:
    case Up.Said{+ig}:
      rm.srcs(srcs, old, dd, tt, ig, se, rb)
    case Up.Unsaid{_w}:
      {==}
    case Up.Unasked{_a}:
      {==}

# LAW: and once every pin is answered, or still asks
law rm.asks:
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +old: M.Manifest
  for +dd: Up.Deps
  for tt: Up.Tools
  for se: {String.is_empty(Up.next.stop(Up.pins.asks(asks, rs, old, dd, tt))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.pins.asks(asks, rs, old, dd, tt)) == Up.next.model(Up.pins.asks(asks, rs, old, dd, tt))
    : M.Read}

def rm.asks(asks, rs, old, dd, tt, se, rb):
  match asks:
    case []:
      rm.ignore(Up.text.said(rs, Up.Ignore{}), Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd)), rs),
        old, dd, tt, se, rb)
    case _h <> _t:
      {==}

# LAW: and whether a pin refused
law rm.bad:
  for clean: Bool
  for +bad: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +old: M.Manifest
  for +dd: Up.Deps
  for tt: Up.Tools
  for se: {String.is_empty(Up.next.stop(Up.pins.bad(clean, bad, asks, rs, old, dd, tt))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.pins.bad(clean, bad, asks, rs, old, dd, tt))
    == Up.next.model(Up.pins.bad(clean, bad, asks, rs, old, dd, tt)) : M.Read}

def rm.bad(clean, _bad, asks, rs, old, dd, tt, se, rb):
  match clean:
    case True{}:
      rm.asks(asks, rs, old, dd, tt, se, rb)
    case False{}:
      {==}

# LAW: the pins' answers together
law rm.pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old: M.Manifest
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, old))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.pins(dd, tt, rs, old)) == Up.next.model(Up.pins(dd, tt, rs, old)) : M.Read}

def rm.pins(dd, tt, rs, old, se, rb):
  match dd tt:
    case Up.Deps{ds, ss, es, dm, dsy, dtr, dasks, +dbad} Up.Tools{ts, tm, tsy, tasks, +tbad}:
      rm.bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
        Bool.pick(String, String.is_empty(dbad), tbad, dbad),
        List.append(&2, Up.Ask, dasks, tasks), rs, old,
        Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}, se, rb)

# LAW: whether `--package` names something
law rm.known:
  for k: Bool
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +old: M.Manifest
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, old))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.known(k, only, rs, old)) == Up.next.model(Up.known(k, only, rs, old)) : M.Read}

def rm.known(k, only, rs, old, se, rb):
  match k:
    case False{}:
      {==}
    case True{}:
      match old:
        case M.Manifest{+n, +e, +b, +h, +hpa, +hpv, +ds, +ts}:
          rm.pins(Up.deps.walk(rs, only, M.hub.or(h), ds), Up.tools.walk(rs, only, ts), rs,
            M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, se, rb)

# LAW: an upgrade that does not stop makes its lock from the model it renders
law rm.next:
  for +only: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  for rb: D1.ReadsBack()
  {Up.next.read(Up.next(only, r, rs)) == Up.next.model(Up.next(only, r, rs)) : M.Read}

def rm.next(only, r, rs, se, rb):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{+n, +e, +b, +h, +hpa, +hpv, +ds, +ts}:
          rm.known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), only, rs,
            M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, se, rb)

# LAW: so the ledger an upgrade that does not refuse leaves reads back as the
# model it rendered
law u.rb0:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for rb: D1.ReadsBack()
  {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}

def u.rb0(only, here, ledger, listing, replies, ups, ok, rb):
  +nx = Up.next(only, W.parsed(ledger), ups)
  +g = D3.ig.left(Up.next.edits(nx), D3.ig.read(ups))
  Equal.trans(M.Read,
    W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}))),
    W.parsed(D3.ledger.left(Up.next.edits(nx), ledger)),
    Up.next.model(nx),
    Equal.cong(W.World, M.Read, x => W.parsed(W.ledger.of(x)),
      D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
      D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
      u.after(only, here, ledger, listing, replies, ups, ok)),
    Equal.trans(M.Read, W.parsed(D3.ledger.left(Up.next.edits(nx), ledger)), Up.next.read(nx),
      Up.next.model(nx),
      Equal.sym(M.Read, Up.next.read(nx), W.parsed(D3.ledger.left(Up.next.edits(nx), ledger)),
        Equal.cong(Up.Next & M.Read, M.Read, q => core.snd(q),
          M2.core.lhs(nx, only, g, ups), M2.core.rhs(nx, g, ledger),
          M2.core(W.parsed(ledger), only, ups, g, ledger, {==}, u.se(only, here, ledger, listing, replies, ups, ok)))),
      rm.next(only, W.parsed(ledger), ups, u.se(only, here, ledger, listing, replies, ups, ok), rb)))

# LAW: the second upgrade decides the target
law u.e2:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
  {M2.view(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
    M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)),
      ups))) == M3.target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), D3.ig.read(ups))) : Up.Next}

def u.e2(only, here, ledger, listing, replies, ups, ok, rb):
  Equal.trans(Up.Next, M2.view(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
    ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
      M2.view(Up.next(only, Up.next.model(Up.next(only, W.parsed(ledger), ups)),
        M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
          M3.target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
            W.parsed(ledger), ups)), D3.ig.read(ups))),
    Equal.cong(M.Read, Up.Next, r => M2.view(Up.next(only, r, M2.re(D3.ig.left(Up.next.edits(Up.next(only,
      W.parsed(ledger), ups)), D3.ig.read(ups)), ups))), W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), ledger)), Up.next.model(Up.next(only, W.parsed(ledger), ups)),
      u.rb(only, here, ledger, listing, replies, ups, ok, rb)),
    Equal.cong(Up.Next & M.Read, Up.Next, q => core.fst(q),
      M2.core.lhs(Up.next(only, W.parsed(ledger), ups), only, D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger),
        ups)), D3.ig.read(ups)), ups), M2.core.rhs(Up.next(only, W.parsed(ledger), ups),
          D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ledger),
      M2.core(W.parsed(ledger), only, ups, D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
        D3.ig.read(ups)), ledger, {==}, u.se(only, here, ledger, listing, replies, ups, ok))))

# LAW: and the first one's lock was made from its model
law u.rm:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
  {Up.next.read(Up.next(only, W.parsed(ledger), ups)) == Up.next.model(Up.next(only, W.parsed(ledger), ups)) : M.Read}

def u.rm(only, here, ledger, listing, replies, ups, ok, rb):
  Equal.trans(M.Read, Up.next.read(Up.next(only, W.parsed(ledger), ups)),
    W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
      Up.next.model(Up.next(only, W.parsed(ledger), ups)),
    Equal.cong(Up.Next & M.Read, M.Read, q => core.snd(q),
      M2.core.lhs(Up.next(only, W.parsed(ledger), ups), only, D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger),
        ups)), D3.ig.read(ups)), ups), M2.core.rhs(Up.next(only, W.parsed(ledger), ups),
          D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ledger),
      M2.core(W.parsed(ledger), only, ups, D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
        D3.ig.read(ups)), ledger, {==}, u.se(only, here, ledger, listing, replies, ups, ok))),
    u.rb(only, here, ledger, listing, replies, ups, ok, rb))

# LAW: so the second decides the target of the ledger the first lock read
law u.e2r:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
  {M2.view(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
    M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)),
      ups))) == M3.target(Up.next.read(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), D3.ig.read(ups))) : Up.Next}

def u.e2r(only, here, ledger, listing, replies, ups, ok, rb):
  Equal.trans(Up.Next, M2.view(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
    ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
      M3.target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), D3.ig.read(ups))), M3.target(Up.next.read(Up.next(only, W.parsed(ledger), ups)),
          D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups))),
    u.e2(only, here, ledger, listing, replies, ups, ok, rb),
    Equal.cong(M.Read, Up.Next, m => M3.target(m, D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
      D3.ig.read(ups))), Up.next.model(Up.next(only, W.parsed(ledger), ups)), Up.next.read(Up.next(only,
        W.parsed(ledger), ups)),
      Equal.sym(M.Read, Up.next.read(Up.next(only, W.parsed(ledger), ups)), Up.next.model(Up.next(only,
        W.parsed(ledger), ups)), u.rm(only, here, ledger, listing, replies, ups, ok, rb))))

# LAW: the lock, run again after an upgrade that did not refuse
law u.idem.ok:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
  {P.put(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
    "ez.lock.toml") == P.put(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups},
      "ez.lock.toml") : P.Wrote}

def u.idem.ok(only, here, ledger, listing, replies, ups, ok, rb):
  L2.lock_reproducible(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
    W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups},
    after_inputs(Up.next(only, W.parsed(ledger), ups), Up.next(only,
      W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
        M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups)),
          D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), listing, replies,
            u.e2r(only, here, ledger, listing, replies, ups, ok, rb),
      empty_nil(Up.next.stop(Up.next(only, W.parsed(ledger), ups)), u.se(only, here, ledger, listing, replies,
        ups, ok))))

# LAW: either way
law u.idem:
  for b: Bool
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +e: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == b : Bool}
  for rb: D1.ReadsBack()
  {P.put(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
    "ez.lock.toml") == P.put(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups},
      "ez.lock.toml") : P.Wrote}

def u.idem(b, only, here, ledger, listing, replies, ups, e, rb):
  match b:
    case True{}:
      ne = Equal.sym(Bool, P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}), True{}, e)
      %ne : {P.put(D3.after.up.pick(_, W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
        "ez.lock.toml") == P.put(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups},
          "ez.lock.toml") : P.Wrote}
      {==}
    case False{}:
      Equal.trans(P.Wrote, P.put(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
        "ez.lock.toml"), P.put(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
          "ez.lock.toml"),
        P.put(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}, "ez.lock.toml"),
        Equal.cong(W.World, P.Wrote, x => P.put(x, "ez.lock.toml"), D3.after(W.World{W.Args{True{}, only,
          here}, ledger,
          listing, replies, ups}), D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing,
            replies, ups}),
          u.after(only, here, ledger, listing, replies, ups, e)),
        u.idem.ok(only, here, ledger, listing, replies, ups, e,
          u.rb0(only, here, ledger, listing, replies, ups, e, rb)))

def Laws.upgrade_idempotent(w, u, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.put(D3.after(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups}),
                "ez.lock.toml") == P.put(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups},
                "ez.lock.toml") : P.Wrote}, u)
            case True{}:
              u.idem(P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}), only, here,
                ledger, listing,
                replies, ups, {==}, rb)

# LAW: the model, either way
law u.moves:
  for b: Bool
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +e: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == b : Bool}
  for rb: D1.ReadsBack()
  {P.ledger.next(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
    ups})) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}

def u.moves(b, only, here, ledger, listing, replies, ups, e, rb):
  match b:
    case True{}:
      ne = Equal.sym(Bool, P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}), True{}, e)
      %ne : {P.ledger.next(D3.after.up.pick(_, W.World{W.Args{True{}, only, here}, ledger, listing, replies,
        ups})) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
      {==}
    case False{}:
      Equal.trans(M.Read, P.ledger.next(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups})),
        P.ledger.next(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups})),
          Up.next.model(Up.next(only, W.parsed(ledger), ups)),
        Equal.cong(W.World, M.Read, x => P.ledger.next(x), D3.after(W.World{W.Args{True{}, only, here},
          ledger, listing,
          replies, ups}), D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
          u.after(only, here, ledger, listing, replies, ups, e)),
        Equal.trans(M.Read, Up.next.model(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
          W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
            D3.ig.read(ups)), ups))), Up.next.model(M2.view(Up.next(only,
              W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
                M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups)))),
                  Up.next.model(Up.next(only, W.parsed(ledger), ups)),
          Equal.sym(M.Read, Up.next.model(M2.view(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
            W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
              D3.ig.read(ups)), ups)))), Up.next.model(Up.next(only,
                W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
                  M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
                    view_model(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
                      ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                        D3.ig.read(ups)), ups)))),
          Equal.cong(Up.Next, M.Read, x => Up.next.model(x), M2.view(Up.next(only,
            W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
              M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
                M3.target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
                  W.parsed(ledger), ups)), D3.ig.read(ups))),
            u.e2(only, here, ledger, listing, replies, ups, e,
              u.rb0(only, here, ledger, listing, replies, ups, e, rb)))))

def Laws.reupgrade_moves_nothing(w, u, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.ledger.next(D3.after(W.World{W.Args{False{}, only, here}, ledger, listing, replies,
                ups})) == P.ledger.next(W.World{W.Args{False{}, only, here}, ledger, listing, replies,
                  ups}) : M.Read}, u)
            case True{}:
              u.moves(P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}), only,
                here, ledger, listing,
                replies, ups, {==}, rb)

# LAW: what the second upgrade's plan leaves at a path, through its view
law u.put:
  for +nx2: Up.Next
  for +listing2: W.Listing
  for +replies2: List<&2, W.Reply>
  for +md: M.Read
  for +g: String
  for +p: String
  for e: {M2.view(nx2) == M3.target(md, g) : Up.Next}
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.plan.of(nx2, listing2, replies2), p) == P.Kept{} : P.Wrote}

def u.put(nx2, listing2, replies2, md, g, p, e, ng, nl):
  +cs = P.cloned(W.replies.of(nx2, replies2))
  +js = W.judged.of(nx2, replies2)
  +dc = P.decide(W.Inputs{Up.next.read(nx2), Up.next.stop(nx2), W.listing.of(nx2, listing2), js})
  Equal.trans(P.Wrote, P.put.plan(P.made(nx2, cs, js, dc), p), P.put.plan(P.made(M2.view(nx2), cs, js, dc), p),
    P.Kept{},
    Equal.sym(P.Wrote, P.put.plan(P.made(M2.view(nx2), cs, js, dc), p), P.put.plan(P.made(nx2, cs, js, dc), p),
      view_put(nx2, cs, js, dc, p)),
    Equal.trans(P.Wrote, P.put.plan(P.made(M2.view(nx2), cs, js, dc), p),
      P.put.plan(P.made(M3.target(md, g), cs, js, dc), p), P.Kept{},
      Equal.cong(Up.Next, P.Wrote, x => P.put.plan(P.made(x, cs, js, dc), p), M2.view(nx2), M3.target(md, g), e),
      target_put(md, g, cs, js, dc, p, ng, nl)))

# LAW: and when it writes no `.gitignore`
law u.put.clean:
  for +nx2: Up.Next
  for +listing2: W.Listing
  for +replies2: List<&2, W.Reply>
  for +md: M.Read
  for +g: String
  for +p: String
  for e: {M2.view(nx2) == M3.target(md, g) : Up.Next}
  for eg: {M3.gi.of(md, g) == [] : List<&2, Up.Edit>}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.plan.of(nx2, listing2, replies2), p) == P.Kept{} : P.Wrote}

def u.put.clean(nx2, listing2, replies2, md, g, p, e, eg, nl):
  +cs = P.cloned(W.replies.of(nx2, replies2))
  +js = W.judged.of(nx2, replies2)
  +dc = P.decide(W.Inputs{Up.next.read(nx2), Up.next.stop(nx2), W.listing.of(nx2, listing2), js})
  Equal.trans(P.Wrote, P.put.plan(P.made(nx2, cs, js, dc), p), P.put.plan(P.made(M2.view(nx2), cs, js, dc), p),
    P.Kept{},
    Equal.sym(P.Wrote, P.put.plan(P.made(M2.view(nx2), cs, js, dc), p), P.put.plan(P.made(nx2, cs, js, dc), p),
      view_put(nx2, cs, js, dc, p)),
    Equal.trans(P.Wrote, P.put.plan(P.made(M2.view(nx2), cs, js, dc), p),
      P.put.plan(P.made(M3.target(md, g), cs, js, dc), p), P.Kept{},
      Equal.cong(Up.Next, P.Wrote, x => P.put.plan(P.made(x, cs, js, dc), p), M2.view(nx2), M3.target(md, g), e),
      target_put.clean(md, g, cs, js, dc, p, eg, nl)))

# LAW: an `or` of a `not` of True is its right half
law or_not_true:
  for c: Bool
  for +x: Bool
  for ec: {c == True{} : Bool}
  for e: {Bool.or(Bool.not(c), x) == True{} : Bool}
  {x == True{} : Bool}

def or_not_true(c, x, ec, e):
  match c:
    case True{}:
      e
    case False{}:
      Eq.bit.absurd(&2, {x == True{} : Bool}, ec)

def Laws.upgrade_settles(w, u, ok, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.put(D3.after(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups}),
                "ez.toml") == P.Kept{} : P.Wrote}, u)
            case True{}:
              Equal.trans(P.Wrote, P.put(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
                "ez.toml"), P.put(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing,
                  replies, ups}),
                  "ez.toml"), P.Kept{},
                Equal.cong(W.World, P.Wrote, x => P.put(x, "ez.toml"), D3.after(W.World{W.Args{True{}, only, here},
                  ledger, listing, replies, ups}), D3.after.up.laid(W.World{W.Args{True{}, only, here},
                    ledger, listing,
                    replies, ups}),
                  u.after(only, here, ledger, listing, replies, ups, ok)),
                u.put(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                  ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)),
                    ups)), W.listing.of(Up.next(only, W.parsed(ledger), ups), listing),
                  D3.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
                    W.parsed(ledger), ups)), W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)),
                  Up.next.model(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
                    W.parsed(ledger), ups)), D3.ig.read(ups)), "ez.toml", u.e2(only, here, ledger, listing,
                      replies, ups,
                      ok, u.rb0(only, here, ledger, listing, replies, ups, ok, rb)), {==}, {==}))

def Laws.reupgrade_writes_only_lock(w, p, u, ok, ev, ne, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.put(D3.after(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups}),
                p) == P.Kept{} : P.Wrote}, u)
            case True{}:
              Equal.trans(P.Wrote, P.put(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing,
                replies, ups}), p),
                P.put(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
                  p), P.Kept{},
                Equal.cong(W.World, P.Wrote, x => P.put(x, p), D3.after(W.World{W.Args{True{}, only, here}, ledger,
                  listing, replies, ups}), D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger,
                    listing, replies,
                    ups}),
                  u.after(only, here, ledger, listing, replies, ups, ok)),
                u.put.clean(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
                  ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                    D3.ig.read(ups)), ups)), W.listing.of(Up.next(only, W.parsed(ledger), ups), listing),
                  D3.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
                    W.parsed(ledger), ups)), W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)),
                  Up.next.model(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
                    W.parsed(ledger), ups)), D3.ig.read(ups)), p, u.e2(only, here, ledger, listing, replies,
                      ups, ok, u.rb0(only, here, ledger, listing, replies, ups, ok, rb)),
                  edits_nil(M3.gi.of(Up.next.model(Up.next(only, W.parsed(ledger), ups)),
                    D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups))),
                    or_not_true(Str.clear.all(I.vended(D2.ledger.deps(Up.next.model(Up.next(only, W.parsed(ledger),
                      ups)))), '\n'),
                      List.is_empty(&2, Up.Edit, M3.gi.of(Up.next.model(Up.next(only, W.parsed(ledger), ups)),
                        D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)))), ev,
                      g.top(W.parsed(ledger), only, ups, u.se(only, here, ledger, listing, replies, ups, ok)))),
                  ne))

# LAW: the second upgrade reads each tree the first laid from BEND_LIB
law u.fresh:
  for +only: String
  for +here: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}) : M.Read}
  {Laws.fresh.origins(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups})) == [] : List<&2,
      String>}

def u.fresh(only, here, ledger, listing, replies, ups, ok, rb):
  +rs1 = W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)
  +er = Equal.trans(M.Read, Up.next.read(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
    W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
      D3.ig.read(ups)), ups))), Up.next.read(M2.view(Up.next(only,
        W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
          M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups)))),
            Up.next.read(Up.next(only, W.parsed(ledger), ups)),
    Equal.sym(M.Read, Up.next.read(M2.view(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
      W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
        D3.ig.read(ups)), ups)))), Up.next.read(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
          W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
            D3.ig.read(ups)), ups))), view_read(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
              W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                D3.ig.read(ups)), ups)))),
    Equal.cong(Up.Next, M.Read, x => Up.next.read(x), M2.view(Up.next(only,
      W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
        M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
          M3.target(Up.next.read(Up.next(only, W.parsed(ledger), ups)), D3.ig.left(Up.next.edits(Up.next(only,
            W.parsed(ledger), ups)), D3.ig.read(ups))),
      u.e2r(only, here, ledger, listing, replies, ups, ok, rb)))
  Equal.trans(List<&2, String>, Laws.fresh.origins(D3.after(W.World{W.Args{True{}, only, here}, ledger, listing,
    replies, ups})),
    Laws.fresh.origins(D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups})), [],
    Equal.cong(W.World, List<&2, String>, x => Laws.fresh.origins(x), D3.after(W.World{W.Args{True{}, only, here},
        ledger,
      listing, replies, ups}), D3.after.up.laid(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}),
      u.after(only, here, ledger, listing, replies, ups, ok)),
    Equal.trans(List<&2, String>,
      Laws.fresh.all(L.ledger.read(Up.next.read(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
          D3.ig.read(ups)), ups)))), M.hub_of(Up.next.read(Up.next(only,
            W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
              M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups)))),
        D3.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
          W.parsed(ledger), ups)), rs1)),
      Laws.fresh.all(L.ledger.read(Up.next.read(Up.next(only, W.parsed(ledger), ups))),
        M.hub_of(Up.next.read(Up.next(only, W.parsed(ledger), ups))),
        D3.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
          W.parsed(ledger), ups)), rs1)),
      [],
      Equal.cong(M.Read, List<&2, String>,
        r => Laws.fresh.all(L.ledger.read(r), M.hub_of(r),
          D3.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
            W.parsed(ledger), ups)), rs1)),
        Up.next.read(Up.next(only, W.parsed(D3.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
          ledger)), M2.re(D3.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), D3.ig.read(ups)), ups))),
            Up.next.read(Up.next(only, W.parsed(ledger), ups)), er),
      fresh.all_after(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only, W.parsed(ledger),
        ups)), rs1)))

def Laws.reupgrade_lays_nothing(w, u, ok, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {Laws.fresh.origins(D3.after(W.World{W.Args{False{}, only, here}, ledger, listing,
                  replies,
                ups})) == [] : List<&2, String>}, u)
            case True{}:
              u.fresh(only, here, ledger, listing, replies, ups, ok,
                u.rb0(only, here, ledger, listing, replies, ups, ok, rb))
