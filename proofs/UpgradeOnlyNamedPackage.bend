# proofs of laws/UpgradeOnlyNamedPackage.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/upgrade.bend as U
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../laws/UpgradeOnlyNamedPackage.bend as Laws
import ../laws/defs/LockInputs.bend as D1
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/UpgradeKeepsNames.bend as M2

# The upgrade's decisions: what it keeps (laws/UpgradeHoldsHub.bend,
# laws/UpgradeOnlyNamedPackage.bend) and what it asks
# (laws/UpgradeOnlyNamedPackage.bend). The upgrade walks the ledger's
# dependencies and tools one at a time, each by what `U.aim` makes of it, so
# every law is a lemma about one entry's fate, an induction over the list,
# and a pass through the pipeline `Up.next` runs the two walks through,
# which leaves the ledger model either as it was or with the walked lists in
# place of the old ones.

# LAW: string equality reads the same either way round
law eq_sym:
  for +a: String
  for +b: String
  {String.eq(a, b) == String.eq(b, a) : Bool}

# LAW: with the first answer given
law eq_sym.go:
  for c: Bool
  for +a: String
  for +b: String
  for +e: {String.eq(a, b) == c : Bool}
  {c == String.eq(b, a) : Bool}

# LAW: and a second that cannot be True when the first was False
law eq_sym.no:
  for d: Bool
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == False{} : Bool}
  for f: {String.eq(b, a) == d : Bool}
  {False{} == d : Bool}

def eq_sym.no(d, a, b, e, f):
  match d:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool},
        Equal.trans(Bool, True{}, String.eq(a, b), False{},
          Equal.trans(Bool, True{}, String.eq(a, a), String.eq(a, b),
            Equal.sym(Bool, String.eq(a, a), True{}, Eq.string_eq_self(a)),
            Equal.cong(String, Bool, x => String.eq(a, x), a, b,
              Equal.sym(String, b, a, Str.string_eq_true(b, a, f)))),
          e))

def eq_sym.go(c, a, b, e):
  match c:
    case True{}:
      ab = Str.string_eq_true(a, b, e)
      %ab : {True{} == String.eq(_, a) : Bool}
      Equal.sym(Bool, String.eq(a, a), True{}, Eq.string_eq_self(a))
    case False{}:
      eq_sym.no(String.eq(b, a), a, b, e, {==})

def eq_sym(a, b):
  eq_sym.go(String.eq(a, b), a, b, {==})

# LAW: a nonempty `--package n` does not choose a name `n` is not
law unchosen:
  for +n: String
  for +m: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {U.chosen(n, m) == False{} : Bool}

def unchosen(n, m, ne, d):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {U.chosen.go(_, n, m) == False{} : Bool}
  d

# LAW: and whether it chooses a name is the name read against it
law chosen_named:
  for +n: String
  for +x: String
  for ne: {String.is_empty(n) == False{} : Bool}
  {U.chosen(n, x) == String.eq(x, n) : Bool}

def chosen_named(n, x, ne):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {U.chosen.go(_, n, x) == String.eq(x, n) : Bool}
  eq_sym(n, x)

# LAW: an entry that is not chosen is held
law unchosen_holds:
  for +n: String
  for +m: String
  for s: M.Source
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {U.aim(U.chosen(n, m), s) == U.Hold{} : U.Aim}

def unchosen_holds(n, m, s, ne, d):
  us = Equal.sym(Bool, U.chosen(n, m), False{}, unchosen(n, m, ne, d))
  %us : {U.aim(_, s) == U.Hold{} : U.Aim}
  {==}

# laws/UpgradeOnlyNamedPackage.bend, the dependencies. One of another name
# is not chosen, so it is held, and the walk leaves it as it was.

law frame_read:
  for +n: String
  for +m: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +ne: {String.is_empty(n) == False{} : Bool}
  for +d: {String.eq(n, m) == False{} : Bool}
  {M.dep(Up.next.model(Up.next(n, r, rs)), m) == M.dep(r, m) : M.Dep}

def frame_read(n, m, r, rs, ne, d):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{mm}:
      match mm:
        case M.Manifest{+pn, +pe, +pb, +hb, +hbpa, +hbpv, +ods, +ots}:
          M2.next_kept(M.Dep, x => M.dep(x, m), n, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots,
            M2.find_walk(rs, n, M.hub.or(hb), ods, m,
              unchosen_holds(n, m, M.source.dep(M.find(ods, m)), ne, d)))

def Laws.upgrade_one_frames_deps(w, n, m, e, ne, d):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              {==}
            case True{}:
              es = Equal.sym(String, only, n, e)
              %es : {M.dep(Up.next.model(Up.next(_, W.parsed(ledger), ups)), m)
                == M.dep(W.parsed(ledger), m) : M.Dep}
              frame_read(n, m, W.parsed(ledger), ups, ne, d)

# LAW: a tool of another name, in front of the rest, is passed over
law tskip_find:
  for t: M.Cli
  for +ts: List<&2, M.Cli>
  for +x: String
  for +m: String
  for nf: {M.tool.name(t) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.tool.find(t <> ts, m) == M.tool.find(ts, m) : M.Cli}

def tskip_find(t, ts, x, m, nf, ne):
  match t:
    case M.Cli{+tn, +te, +tb, +tsrc}:
      nfs = Equal.sym(String, tn, x, nf)
      %nfs : {M.tool.find.pick(String.eq(_, m), M.Cli{tn, te, tb, tsrc}, M.tool.find(ts, m))
        == M.tool.find(ts, m) : M.Cli}
      nes = Equal.sym(Bool, String.eq(x, m), False{}, ne)
      %nes : {M.tool.find.pick(_, M.Cli{tn, te, tb, tsrc}, M.tool.find(ts, m))
        == M.tool.find(ts, m) : M.Cli}
      {==}

# LAW: a pin of another name, joined in front of the rest, is passed over by
# a lookup
law tjoin_skip:
  for p: Up.Pinned
  for r: Up.Tools
  for +x: String
  for +m: String
  for nf: {M1.pinned.name(p, x) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.tool.find(M2.tools.of(Up.tools.join(p, r)), m) == M.tool.find(M2.tools.of(r), m) : M.Cli}

def tjoin_skip(p, r, x, m, nf, ne):
  match p:
    case Up.Pinned{t, mv, says}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          tskip_find(t, ts, x, m, nf, ne)
    case Up.PinWait{more}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}
    case Up.PinHalt{why}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}

# LAW: a tool that is not chosen, joined in front of the rest, is the one a
# lookup of its name finds
law left_find:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tn: String
  for +te: String
  for +tb: String
  for +tsrc: M.Source
  for r: Up.Tools
  for +m: String
  for e: {String.eq(tn, m) == True{} : Bool}
  for h: {sel == False{} : Bool}
  {M.tool.find(M2.tools.of(Up.tools.join(Up.tool.sel(sel, rs, M.Cli{tn, te, tb, tsrc}), r)), m)
    == M.Cli{tn, te, tb, tsrc} : M.Cli}

def left_find(sel, rs, tn, te, tb, tsrc, r, m, e, h):
  match r:
    case Up.Tools{+ts, +any, +sy, +asks, +bad}:
      hsym = Equal.sym(Bool, sel, False{}, h)
      %hsym : {M.tool.find(M2.tools.of(Up.tools.join(Up.tool.sel(_, rs, M.Cli{tn, te, tb, tsrc}),
        Up.Tools{ts, any, sy, asks, bad})), m) == M.Cli{tn, te, tb, tsrc} : M.Cli}
      es2 = Equal.sym(Bool, String.eq(tn, m), True{}, e)
      %es2 : {M.tool.find.pick(_, M.Cli{tn, te, tb, tsrc}, M.tool.find(ts, m))
        == M.Cli{tn, te, tb, tsrc} : M.Cli}
      {==}

law tfind_walk.hit:
  for hit: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +tn: String
  for +te: String
  for +tb: String
  for +tsrc: M.Source
  for +t: List<&2, M.Cli>
  for +m: String
  for +e: {String.eq(tn, m) == hit : Bool}
  for pre: {U.chosen(only, m) == False{} : Bool}
  for ih: {M.tool.find(M2.tools.of(Up.tools.walk(rs, only, t)), m) == M.tool.find(t, m) : M.Cli}
  {M.tool.find(M2.tools.of(Up.tools.join(Up.tool.sel(U.chosen(only, tn), rs, M.Cli{tn, te, tb, tsrc}),
    Up.tools.walk(rs, only, t))), m)
    == M.tool.find.pick(hit, M.Cli{tn, te, tb, tsrc}, M.tool.find(t, m)) : M.Cli}

def tfind_walk.hit(hit, rs, only, tn, te, tb, tsrc, t, m, e, pre, ih):
  match hit:
    case True{}:
      left_find(U.chosen(only, tn), rs, tn, te, tb, tsrc, Up.tools.walk(rs, only, t), m, e,
        Equal.trans(Bool, U.chosen(only, tn), U.chosen(only, m), False{},
          Equal.cong(String, Bool, x => U.chosen(only, x), tn, m, Str.string_eq_true(tn, m, e)),
          pre))
    case False{}:
      Equal.trans(M.Cli,
        M.tool.find(M2.tools.of(Up.tools.join(Up.tool.sel(U.chosen(only, tn), rs,
          M.Cli{tn, te, tb, tsrc}), Up.tools.walk(rs, only, t))), m),
        M.tool.find(M2.tools.of(Up.tools.walk(rs, only, t)), m),
        M.tool.find(t, m),
        tjoin_skip(Up.tool.sel(U.chosen(only, tn), rs, M.Cli{tn, te, tb, tsrc}),
          Up.tools.walk(rs, only, t), tn, m,
          M1.sel_name(U.chosen(only, tn), rs, M.Cli{tn, te, tb, tsrc}), e),
        ih)

# LAW: the walk leaves every tool of a name `--package` does not choose as it
# was
law tfind_walk:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for ts: List<&2, M.Cli>
  for +m: String
  for +pre: {U.chosen(only, m) == False{} : Bool}
  {M.tool.find(M2.tools.of(Up.tools.walk(rs, only, ts)), m) == M.tool.find(ts, m) : M.Cli}

def tfind_walk(rs, only, ts, m, pre):
  match ts:
    case []:
      {==}
    case h <> +t:
      match h:
        case M.Cli{+tn, +te, +tb, +tsrc}:
          tfind_walk.hit(String.eq(tn, m), rs, only, tn, te, tb, tsrc, t, m, {==}, pre,
            tfind_walk(rs, only, t, m, pre))

law tframe_read:
  for +n: String
  for +m: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {Laws.tool.at(Up.next.model(Up.next(n, r, rs)), m) == Laws.tool.at(r, m) : M.Cli}

def tframe_read(n, m, r, rs, ne, d):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{mm}:
      match mm:
        case M.Manifest{+pn, +pe, +pb, +hb, +hbpa, +hbpv, +ods, +ots}:
          M2.next_kept(M.Cli, x => Laws.tool.at(x, m), n, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots,
            tfind_walk(rs, n, ots, m, unchosen(n, m, ne, d)))

def Laws.upgrade_one_frames_tools(w, n, m, e, ne, d):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              {==}
            case True{}:
              es = Equal.sym(String, only, n, e)
              %es : {Laws.tool.at(Up.next.model(Up.next(_, W.parsed(ledger), ups)), m)
                == Laws.tool.at(W.parsed(ledger), m) : M.Cli}
              tframe_read(n, m, W.parsed(ledger), ups, ne, d)

# laws/UpgradeOnlyNamedPackage.bend, the questions. What the upgrade asks is
# read off the two walks only through their keys: the questions each left
# open, its refusal, and the hashes import lines stop naming. An entry
# `--package` does not choose is held, and a held entry adds nothing to any
# of the three, so the walk over the ledger and the walk over the entries
# named `n` alone have the same keys, and the pipeline asks the same
# questions of both.

# the part of a dependency walk the questions depend on
def dkey(dd: Up.Deps) -> Up.Deps:
  Up.Deps{_ds, _ss, es, _m, _sy, _tr, asks, bad} = dd
  Up.Deps{[], [], es, False{}, [], [], asks, bad}

# and of a tool walk
def tkey(tt: Up.Tools) -> Up.Tools:
  Up.Tools{_ts, _m, _sy, asks, bad} = tt
  Up.Tools{[], False{}, [], asks, bad}

# LAW: one dependency joined in front of a walk adds to its key what it adds
# to the key alone
law djoin_key:
  for f: Up.Fate
  for r: Up.Deps
  {dkey(Up.deps.join(f, r)) == dkey(Up.deps.join(f, dkey(r))) : Up.Deps}

def djoin_key(f, r):
  match f:
    case Up.Became{d, old, new, prev, mv, says, trees}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}
    case Up.Waits{more}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}
    case Up.Halts{why}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}

# LAW: so two walks with one key, each with the same dependency in front,
# still have one key
law djoin_cong:
  for +f: Up.Fate
  for +r1: Up.Deps
  for +r2: Up.Deps
  for ih: {dkey(r1) == dkey(r2) : Up.Deps}
  {dkey(Up.deps.join(f, r1)) == dkey(Up.deps.join(f, r2)) : Up.Deps}

def djoin_cong(f, r1, r2, ih):
  Equal.trans(Up.Deps, dkey(Up.deps.join(f, r1)), dkey(Up.deps.join(f, dkey(r1))),
    dkey(Up.deps.join(f, r2)),
    djoin_key(f, r1),
    Equal.trans(Up.Deps, dkey(Up.deps.join(f, dkey(r1))), dkey(Up.deps.join(f, dkey(r2))),
      dkey(Up.deps.join(f, r2)),
      Equal.cong(Up.Deps, Up.Deps, k => dkey(Up.deps.join(f, k)), dkey(r1), dkey(r2), ih),
      Equal.sym(Up.Deps, dkey(Up.deps.join(f, r2)), dkey(Up.deps.join(f, dkey(r2))),
        djoin_key(f, r2))))

# LAW: a held dependency adds nothing to the key
law ddrop:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for r: Up.Deps
  {dkey(Up.deps.join(Up.dep.one(U.Hold{}, rs, only, hub, h), r)) == dkey(r) : Up.Deps}

def ddrop(_rs, _only, _hub, _h, r):
  match r:
    case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
      {==}

law dalone_walk.hit:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hub: String
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for e: {b == U.chosen(n, M.dep.name(h)) : Bool}
  for ih: {dkey(Up.deps.walk(rs, n, hub, t)) == dkey(Up.deps.walk(rs, n, hub, D1.deps.named(t, n)))
    : Up.Deps}
  {dkey(Up.deps.walk(rs, n, hub, h <> t))
    == dkey(Up.deps.walk(rs, n, hub, D1.deps.put(b, h, D1.deps.named(t, n)))) : Up.Deps}

def dalone_walk.hit(b, rs, n, hub, h, t, e, ih):
  match b:
    case True{}:
      djoin_cong(Up.dep.one(U.aim(U.chosen(n, M.dep.name(h)), M.source.dep(h)), rs, n, hub, h),
        Up.deps.walk(rs, n, hub, t), Up.deps.walk(rs, n, hub, D1.deps.named(t, n)), ih)
    case False{}:
      %e : {dkey(Up.deps.join(Up.dep.one(U.aim(_, M.source.dep(h)), rs, n, hub, h),
        Up.deps.walk(rs, n, hub, t)))
        == dkey(Up.deps.walk(rs, n, hub, D1.deps.named(t, n))) : Up.Deps}
      Equal.trans(Up.Deps,
        dkey(Up.deps.join(Up.dep.one(U.Hold{}, rs, n, hub, h), Up.deps.walk(rs, n, hub, t))),
        dkey(Up.deps.walk(rs, n, hub, t)),
        dkey(Up.deps.walk(rs, n, hub, D1.deps.named(t, n))),
        ddrop(rs, n, hub, h, Up.deps.walk(rs, n, hub, t)),
        ih)

# LAW: the walk over a ledger's dependencies and the walk over those named
# `n` alone have one key
law dalone_walk:
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hub: String
  for ds: List<&2, M.Dep>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {dkey(Up.deps.walk(rs, n, hub, ds)) == dkey(Up.deps.walk(rs, n, hub, D1.deps.named(ds, n)))
    : Up.Deps}

def dalone_walk(rs, n, hub, ds, ne):
  match ds:
    case []:
      {==}
    case +h <> +t:
      dalone_walk.hit(String.eq(M.dep.name(h), n), rs, n, hub, h, t,
        Equal.sym(Bool, U.chosen(n, M.dep.name(h)), String.eq(M.dep.name(h), n),
          chosen_named(n, M.dep.name(h), ne)),
        dalone_walk(rs, n, hub, t, ne))

# LAW: and the tools, the same way
law tjoin_key:
  for p: Up.Pinned
  for r: Up.Tools
  {tkey(Up.tools.join(p, r)) == tkey(Up.tools.join(p, tkey(r))) : Up.Tools}

def tjoin_key(p, r):
  match p:
    case Up.Pinned{t, mv, says}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}
    case Up.PinWait{more}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}
    case Up.PinHalt{why}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}

law tjoin_cong:
  for +p: Up.Pinned
  for +r1: Up.Tools
  for +r2: Up.Tools
  for ih: {tkey(r1) == tkey(r2) : Up.Tools}
  {tkey(Up.tools.join(p, r1)) == tkey(Up.tools.join(p, r2)) : Up.Tools}

def tjoin_cong(p, r1, r2, ih):
  Equal.trans(Up.Tools, tkey(Up.tools.join(p, r1)), tkey(Up.tools.join(p, tkey(r1))),
    tkey(Up.tools.join(p, r2)),
    tjoin_key(p, r1),
    Equal.trans(Up.Tools, tkey(Up.tools.join(p, tkey(r1))), tkey(Up.tools.join(p, tkey(r2))),
      tkey(Up.tools.join(p, r2)),
      Equal.cong(Up.Tools, Up.Tools, k => tkey(Up.tools.join(p, k)), tkey(r1), tkey(r2), ih),
      Equal.sym(Up.Tools, tkey(Up.tools.join(p, r2)), tkey(Up.tools.join(p, tkey(r2))),
        tjoin_key(p, r2))))

law tdrop:
  for +rs: List<&2, Up.Reply>
  for +h: M.Cli
  for r: Up.Tools
  {tkey(Up.tools.join(Up.tool.sel(False{}, rs, h), r)) == tkey(r) : Up.Tools}

def tdrop(_rs, _h, r):
  match r:
    case Up.Tools{ts, any, sy, asks, bad}:
      {==}

law talone_walk.hit:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +h: M.Cli
  for +t: List<&2, M.Cli>
  for e: {b == U.chosen(n, M.tool.name(h)) : Bool}
  for ih: {tkey(Up.tools.walk(rs, n, t)) == tkey(Up.tools.walk(rs, n, D1.tools.named(t, n)))
    : Up.Tools}
  {tkey(Up.tools.walk(rs, n, h <> t))
    == tkey(Up.tools.walk(rs, n, D1.tools.put(b, h, D1.tools.named(t, n)))) : Up.Tools}

def talone_walk.hit(b, rs, n, h, t, e, ih):
  match b:
    case True{}:
      tjoin_cong(Up.tool.sel(U.chosen(n, M.tool.name(h)), rs, h),
        Up.tools.walk(rs, n, t), Up.tools.walk(rs, n, D1.tools.named(t, n)), ih)
    case False{}:
      %e : {tkey(Up.tools.join(Up.tool.sel(_, rs, h), Up.tools.walk(rs, n, t)))
        == tkey(Up.tools.walk(rs, n, D1.tools.named(t, n))) : Up.Tools}
      Equal.trans(Up.Tools,
        tkey(Up.tools.join(Up.tool.sel(False{}, rs, h), Up.tools.walk(rs, n, t))),
        tkey(Up.tools.walk(rs, n, t)),
        tkey(Up.tools.walk(rs, n, D1.tools.named(t, n))),
        tdrop(rs, h, Up.tools.walk(rs, n, t)),
        ih)

law talone_walk:
  for +rs: List<&2, Up.Reply>
  for +n: String
  for ts: List<&2, M.Cli>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {tkey(Up.tools.walk(rs, n, ts)) == tkey(Up.tools.walk(rs, n, D1.tools.named(ts, n)))
    : Up.Tools}

def talone_walk(rs, n, ts, ne):
  match ts:
    case []:
      {==}
    case +h <> +t:
      talone_walk.hit(String.eq(M.tool.name(h), n), rs, n, h, t,
        Equal.sym(Bool, U.chosen(n, M.tool.name(h)), String.eq(M.tool.name(h), n),
          chosen_named(n, M.tool.name(h), ne)),
        talone_walk(rs, n, t, ne))

# `--package n` is checked against the ledger before anything is asked. The
# entries named `n` are all of them that can answer that check.

law kin.hit:
  for b: Bool
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +n: String
  for e: {b == String.eq(M.dep.name(h), n) : Bool}
  for ih: {U.known.in(t, n) == U.known.in(D1.deps.named(t, n), n) : Bool}
  {U.known.step(b, _u => U.known.in(t, n))
    == U.known.in(D1.deps.put(b, h, D1.deps.named(t, n)), n) : Bool}

def kin.hit(b, _h, t, n, e, ih):
  match b:
    case True{}:
      %e : {True{} == U.known.step(_, _u => U.known.in(D1.deps.named(t, n), n)) : Bool}
      {==}
    case False{}:
      ih

law kin:
  for ds: List<&2, M.Dep>
  for +n: String
  {U.known.in(ds, n) == U.known.in(D1.deps.named(ds, n), n) : Bool}

def kin(ds, n):
  match ds:
    case []:
      {==}
    case +h <> +t:
      kin.hit(String.eq(M.dep.name(h), n), h, t, n, {==}, kin(t, n))

# LAW: the ledger names the dependency `--package n` asks for exactly when
# its entries named `n` do
law dknown:
  for +n: String
  for +ds: List<&2, M.Dep>
  for ne: {String.is_empty(n) == False{} : Bool}
  {U.known(n, ds) == U.known(n, D1.deps.named(ds, n)) : Bool}

def dknown(n, ds, ne):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {U.known.go(_, ds, n) == U.known.go(_, D1.deps.named(ds, n), n) : Bool}
  kin(ds, n)

law tkin.hit:
  for b: Bool
  for +h: M.Cli
  for +t: List<&2, M.Cli>
  for +n: String
  for e: {b == String.eq(M.tool.name(h), n) : Bool}
  for ih: {M.tool.has(t, n) == M.tool.has(D1.tools.named(t, n), n) : Bool}
  {M.tool.step(b, _u => M.tool.has(t, n))
    == M.tool.has(D1.tools.put(b, h, D1.tools.named(t, n)), n) : Bool}

def tkin.hit(b, _h, t, n, e, ih):
  match b:
    case True{}:
      %e : {True{} == M.tool.step(_, _u => M.tool.has(D1.tools.named(t, n), n)) : Bool}
      {==}
    case False{}:
      ih

law tkin:
  for ts: List<&2, M.Cli>
  for +n: String
  {M.tool.has(ts, n) == M.tool.has(D1.tools.named(ts, n), n) : Bool}

def tkin(ts, n):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tkin.hit(String.eq(M.tool.name(h), n), h, t, n, {==}, tkin(t, n))

law tknown:
  for +n: String
  for +ts: List<&2, M.Cli>
  for ne: {String.is_empty(n) == False{} : Bool}
  {M.tool.known(n, ts) == M.tool.known(n, D1.tools.named(ts, n)) : Bool}

def tknown(n, ts, ne):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {M.tool.known.go(_, ts, n) == M.tool.known.go(_, D1.tools.named(ts, n), n) : Bool}
  tkin(ts, n)

# The pipeline's questions: after the walks, the upgrade asks for
# `.gitignore` and the sources, or stops, and neither depends on anything but
# the walks' keys.

law asks_done:
  for old1: M.Manifest
  for old2: M.Manifest
  for dd1: Up.Deps
  for dd2: Up.Deps
  for tt1: Up.Tools
  for tt2: Up.Tools
  for +ignore: String
  for +fs: List<&2, Up.Found>
  {Up.next.asks(Up.done(old1, dd1, tt1, ignore, fs)) == Up.next.asks(Up.done(old2, dd2, tt2, ignore, fs))
    : List<&2, Up.Ask>}

def asks_done(old1, old2, dd1, dd2, tt1, tt2, _ignore, _fs):
  match old1:
    case M.Manifest{n1, e1, b1, h1, h1pa, h1pv, ds1, ts1}:
      match old2:
        case M.Manifest{n2, e2, b2, h2, h2pa, h2pv, ds2, ts2}:
          match dd1:
            case Up.Deps{a1, s1, x1, m1, y1, r1, k1, d1}:
              match dd2:
                case Up.Deps{a2, s2, x2, m2, y2, r2, k2, d2}:
                  match tt1:
                    case Up.Tools{u1, v1, w1, p1, q1}:
                      match tt2:
                        case Up.Tools{u2, v2, w2, p2, q2}:
                          {==}

law asks_srcs:
  for srcs: Up.Srcs
  for old1: M.Manifest
  for old2: M.Manifest
  for dd1: Up.Deps
  for dd2: Up.Deps
  for tt1: Up.Tools
  for tt2: Up.Tools
  for +ignore: String
  {Up.next.asks(Up.got.srcs(srcs, old1, dd1, tt1, ignore))
    == Up.next.asks(Up.got.srcs(srcs, old2, dd2, tt2, ignore)) : List<&2, Up.Ask>}

def asks_srcs(srcs, old1, old2, dd1, dd2, tt1, tt2, ignore):
  match srcs:
    case Up.Srcs{fs}:
      asks_done(old1, old2, dd1, dd2, tt1, tt2, ignore, fs)
    case Up.SrcsWait{_ask}:
      {==}
    case Up.SrcsNo{_why}:
      {==}

law asks_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for old1: M.Manifest
  for old2: M.Manifest
  for dd1: Up.Deps
  for dd2: Up.Deps
  for tt1: Up.Tools
  for tt2: Up.Tools
  {Up.next.asks(Up.got.ignore(said, srcs, old1, dd1, tt1))
    == Up.next.asks(Up.got.ignore(said, srcs, old2, dd2, tt2)) : List<&2, Up.Ask>}

def asks_ignore(said, srcs, old1, old2, dd1, dd2, tt1, tt2):
  match said:
    case Up.Said{+ignore}:
      asks_srcs(srcs, old1, old2, dd1, dd2, tt1, tt2, ignore)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law asks_settled:
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for +dd1: Up.Deps
  for +dd2: Up.Deps
  for +tt1: Up.Tools
  for +tt2: Up.Tools
  for e: {Up.deps.edits(dd1) == Up.deps.edits(dd2) : List<&2, U.Swap>}
  {Up.next.asks(Up.settled(rs, old1, dd1, tt1)) == Up.next.asks(Up.settled(rs, old2, dd2, tt2))
    : List<&2, Up.Ask>}

def asks_settled(rs, old1, old2, dd1, dd2, tt1, tt2, e):
  %e : {Up.next.asks(Up.settled(rs, old1, dd1, tt1))
    == Up.next.asks(Up.got.ignore(Up.text.said(rs, Up.Ignore{}),
      Up.ask.srcs(List.is_empty(&2, U.Swap, _), rs), old2, dd2, tt2)) : List<&2, Up.Ask>}
  asks_ignore(Up.text.said(rs, Up.Ignore{}),
    Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd1)), rs), old1, old2, dd1, dd2, tt1, tt2)

law asks_asks:
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for +dd1: Up.Deps
  for +dd2: Up.Deps
  for +tt1: Up.Tools
  for +tt2: Up.Tools
  for e: {Up.deps.edits(dd1) == Up.deps.edits(dd2) : List<&2, U.Swap>}
  {Up.next.asks(Up.pins.asks(asks, rs, old1, dd1, tt1))
    == Up.next.asks(Up.pins.asks(asks, rs, old2, dd2, tt2)) : List<&2, Up.Ask>}

def asks_asks(asks, rs, old1, old2, dd1, dd2, tt1, tt2, e):
  match asks:
    case []:
      asks_settled(rs, old1, old2, dd1, dd2, tt1, tt2, e)
    case _h <> _t:
      {==}

law asks_bad:
  for clean: Bool
  for bad1: String
  for bad2: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for +dd1: Up.Deps
  for +dd2: Up.Deps
  for +tt1: Up.Tools
  for +tt2: Up.Tools
  for e: {Up.deps.edits(dd1) == Up.deps.edits(dd2) : List<&2, U.Swap>}
  {Up.next.asks(Up.pins.bad(clean, bad1, asks, rs, old1, dd1, tt1))
    == Up.next.asks(Up.pins.bad(clean, bad2, asks, rs, old2, dd2, tt2)) : List<&2, Up.Ask>}

def asks_bad(clean, _bad1, _bad2, asks, rs, old1, old2, dd1, dd2, tt1, tt2, e):
  match clean:
    case True{}:
      asks_asks(asks, rs, old1, old2, dd1, dd2, tt1, tt2, e)
    case False{}:
      {==}

# LAW: the questions after the walks are read off their keys
law pins_key:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  {Up.next.asks(Up.pins(dd, tt, rs, old1)) == Up.next.asks(Up.pins(dkey(dd), tkey(tt), rs, old2))
    : List<&2, Up.Ask>}

def pins_key(dd, tt, rs, old1, old2):
  match dd:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad}:
      match tt:
        case Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
          asks_bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            List.append(&2, Up.Ask, das, tas), rs, old1, old2,
            Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Deps{[], [], es, False{}, [], [], [], ""},
            Up.Tools{ts, tm, tsy, [], ""}, Up.Tools{[], False{}, [], [], ""}, {==})

law pins_cong:
  for +k1: Up.Deps
  for +k2: Up.Deps
  for +t1: Up.Tools
  for +t2: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old: M.Manifest
  for ek: {k1 == k2 : Up.Deps}
  for et: {t1 == t2 : Up.Tools}
  {Up.next.asks(Up.pins(k1, t1, rs, old)) == Up.next.asks(Up.pins(k2, t2, rs, old)) : List<&2, Up.Ask>}

def pins_cong(k1, _k2, t1, t2, rs, old, ek, et):
  %ek : {Up.next.asks(Up.pins(k1, t1, rs, old)) == Up.next.asks(Up.pins(_, t2, rs, old))
    : List<&2, Up.Ask>}
  %et : {Up.next.asks(Up.pins(k1, t1, rs, old)) == Up.next.asks(Up.pins(k1, _, rs, old))
    : List<&2, Up.Ask>}
  {==}

# LAW: two pairs of walks with the same keys ask the same questions, whatever
# ledgers they came from
law asks_pins:
  for +dd1: Up.Deps
  for +tt1: Up.Tools
  for +dd2: Up.Deps
  for +tt2: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for ed: {dkey(dd1) == dkey(dd2) : Up.Deps}
  for et: {tkey(tt1) == tkey(tt2) : Up.Tools}
  {Up.next.asks(Up.pins(dd1, tt1, rs, old1)) == Up.next.asks(Up.pins(dd2, tt2, rs, old2))
    : List<&2, Up.Ask>}

def asks_pins(dd1, tt1, dd2, tt2, rs, old1, old2, ed, et):
  Equal.trans(List<&2, Up.Ask>,
    Up.next.asks(Up.pins(dd1, tt1, rs, old1)),
    Up.next.asks(Up.pins(dkey(dd1), tkey(tt1), rs, old1)),
    Up.next.asks(Up.pins(dd2, tt2, rs, old2)),
    pins_key(dd1, tt1, rs, old1, old1),
    Equal.trans(List<&2, Up.Ask>,
      Up.next.asks(Up.pins(dkey(dd1), tkey(tt1), rs, old1)),
      Up.next.asks(Up.pins(dkey(dd2), tkey(tt2), rs, old1)),
      Up.next.asks(Up.pins(dd2, tt2, rs, old2)),
      pins_cong(dkey(dd1), dkey(dd2), tkey(tt1), tkey(tt2), rs, old1, ed, et),
      Equal.sym(List<&2, Up.Ask>, Up.next.asks(Up.pins(dd2, tt2, rs, old2)),
        Up.next.asks(Up.pins(dkey(dd2), tkey(tt2), rs, old1)),
        pins_key(dd2, tt2, rs, old2, old1))))

law asks_known:
  for ok: Bool
  for +n: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {Up.next.asks(Up.known(ok, n, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}))
    == Up.next.asks(Up.known(ok, n, rs,
      M.Manifest{pn, pe, pb, hb, hbpa, hbpv, D1.deps.named(ods, n), D1.tools.named(ots, n)}))
    : List<&2, Up.Ask>}

def asks_known(ok, n, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ne):
  match ok:
    case False{}:
      {==}
    case True{}:
      asks_pins(Up.deps.walk(rs, n, M.hub.or(hb), ods), Up.tools.walk(rs, n, ots),
        Up.deps.walk(rs, n, M.hub.or(hb), D1.deps.named(ods, n)),
        Up.tools.walk(rs, n, D1.tools.named(ots, n)), rs,
        M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots},
        M.Manifest{pn, pe, pb, hb, hbpa, hbpv, D1.deps.named(ods, n), D1.tools.named(ots, n)},
        dalone_walk(rs, n, M.hub.or(hb), ods, ne), talone_walk(rs, n, ots, ne))

# LAW: an upgrade of a ledger asks what an upgrade of its entries named `n`
# alone asks
law asks_next:
  for +n: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {Up.next.asks(Up.next(n, r, rs)) == Up.next.asks(Up.next(n, D1.alone(r, n), rs))
    : List<&2, Up.Ask>}

def asks_next(n, r, rs, ne):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{mm}:
      match mm:
        case M.Manifest{+pn, +pe, +pb, +hb, +hbpa, +hbpv, +ods, +ots}:
          dk = dknown(n, ods, ne)
          %dk : {Up.next.asks(Up.known(Bool.or(U.known(n, ods), M.tool.known(n, ots)), n, rs,
            M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}))
            == Up.next.asks(Up.known(Bool.or(_, M.tool.known(n, D1.tools.named(ots, n))), n, rs,
              M.Manifest{pn, pe, pb, hb, hbpa, hbpv, D1.deps.named(ods, n), D1.tools.named(ots, n)}))
            : List<&2, Up.Ask>}
          tk = tknown(n, ots, ne)
          %tk : {Up.next.asks(Up.known(Bool.or(U.known(n, ods), M.tool.known(n, ots)), n, rs,
            M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}))
            == Up.next.asks(Up.known(Bool.or(U.known(n, ods), _), n, rs,
              M.Manifest{pn, pe, pb, hb, hbpa, hbpv, D1.deps.named(ods, n), D1.tools.named(ots, n)}))
            : List<&2, Up.Ask>}
          asks_known(Bool.or(U.known(n, ods), M.tool.known(n, ots)), n, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots,
            ne)

def Laws.upgrade_one_asks_alone(w, n, u, e, ne):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.wants.up(W.World{W.Args{False{}, only, here}, ledger, listing,
                replies, ups}) == Up.next.asks(Up.next(n, D1.alone(W.parsed(ledger), n),
                Laws.ups.of(W.World{W.Args{False{}, only, here}, ledger, listing, replies, ups})))
                : List<&2, Up.Ask>}, u)
            case True{}:
              es = Equal.sym(String, only, n, e)
              %es : {Up.next.asks(Up.next(_, W.parsed(ledger), ups))
                == Up.next.asks(Up.next(n, D1.alone(W.parsed(ledger), n), ups)) : List<&2, Up.Ask>}
              asks_next(n, W.parsed(ledger), ups, ne)
