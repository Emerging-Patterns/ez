# proofs of laws/AddDependencyIdempotent.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/add/world.bend as A
import ../laws/AddDependencyIdempotent.bend as Laws
import ../laws/LedgerAddIdempotent.bend as L1
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2

# LAW: one step of the lookup past the drop, with the branch the drop takes
# given as a parameter and the equation that put it there alongside. A
# dependency the drop kept has another name, so the lookup passes it by.
law find_last.arm:
  for +h: M.Dep
  for -r: List<&2, M.Dep>
  for +n: String
  for -x: M.Dep
  for b: Bool
  for eb: {String.eq(M.dep.name(h), n) == b : Bool}
  for ih: {M.find(List.append(&2, M.Dep, r, [x]), n) == x : M.Dep}
  {M.find(List.append(&2, M.Dep, Rend.without.put(b, h, r), [x]), n) == x : M.Dep}

def find_last.arm(h, r, n, x, b, eb, ih):
  match h:
    case M.Dep{+hn, hh, he, hs}:
      match b:
        case True{}:
          ih
        case False{}:
          Equal.trans(M.Dep,
            M.find.pick(String.eq(hn, n), M.Dep{hn, hh, he, hs},
              M.find(List.append(&2, M.Dep, r, [x]), n)),
            M.find(List.append(&2, M.Dep, r, [x]), n),
            x,
            Equal.cong(Bool, M.Dep,
              c => M.find.pick(c, M.Dep{hn, hh, he, hs},
                M.find(List.append(&2, M.Dep, r, [x]), n)),
              String.eq(hn, n), False{}, eb),
            ih)

# LAW: a dependency put after every other entry of its name was dropped is
# the one the lookup of that name finds
law find_last:
  for ds: List<&2, M.Dep>
  for +n: String
  for +h: String
  for +e: String
  for +s: M.Source
  {M.find(List.append(&2, M.Dep, Rend.without(ds, n), [M.Dep{n, h, e, s}]), n)
    == M.Dep{n, h, e, s} : M.Dep}

def find_last(ds, n, h, e, s):
  match ds:
    case []:
      Equal.cong(Bool, M.Dep,
        c => M.find.pick(c, M.Dep{n, h, e, s}, M.Dep{"", "", "", M.Hub{""}}),
        String.eq(n, n), True{}, Eq.string_eq_self(n))
    case +d <> t:
      find_last.arm(d, Rend.without(t, n), n, M.Dep{n, h, e, s},
        String.eq(M.dep.name(d), n), {==}, find_last(t, n, h, e, s))

# LAW: keeping the bit a kept source already carries changes nothing. A
# vendored git source says it is vendored, and vendoring it again is itself;
# a hub source is never vendored.
law revend_again:
  for k: Bool
  for s: M.Source
  {Rend.revend(M.source.vendor(Rend.revend(k, s)), s) == Rend.revend(k, s) : M.Source}

def revend_again(k, s):
  match k:
    case True{}:
      match s:
        case M.Hub{_named}:
          {==}
        case M.Git{url, rev, tag, root, nar, vend}:
          {==}
        case M.Member{_path, _named}:
          {==}
    case False{}:
      match s:
        case M.Hub{_named}:
          {==}
        case M.Member{_path, _named}:
          {==}
        case M.Git{url, rev, tag, root, nar, vend}:
          match vend:
            case True{}:
              {==}
            case False{}:
              {==}

# LAW: a dependency added again to the list the first add made is the one the
# first add wrote: the lookup finds that entry, and its bit is kept as it is
law readd_again:
  for +ds: List<&2, M.Dep>
  for +d: M.Dep
  {Rend.readd(List.append(&2, M.Dep, Rend.without(ds, M.dep.name(Rend.readd(ds, d))),
    [Rend.readd(ds, d)]), d) == Rend.readd(ds, d) : M.Dep}

def readd_again(ds, d):
  match d:
    case M.Dep{+n, h, e, s}:
      Equal.cong(M.Source, M.Dep, y => M.Dep{n, h, e, y},
        Rend.revend(M.source.vendor(M.source.dep(M.find(List.append(&2, M.Dep,
          Rend.without(ds, n),
          [M.Dep{n, h, e, Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}]),
          n))), s),
        Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s),
        Equal.trans(M.Source,
          Rend.revend(M.source.vendor(M.source.dep(M.find(List.append(&2, M.Dep,
            Rend.without(ds, n),
            [M.Dep{n, h, e, Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}]),
            n))), s),
          Rend.revend(M.source.vendor(Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)), s),
          Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s),
          Equal.cong(M.Dep, M.Source,
            y => Rend.revend(M.source.vendor(M.source.dep(y)), s),
            M.find(List.append(&2, M.Dep, Rend.without(ds, n),
              [M.Dep{n, h, e, Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}]),
              n),
            M.Dep{n, h, e, Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)},
            find_last(ds, n, h, e,
              Rend.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s))),
          revend_again(M.source.vendor(M.source.dep(M.find(ds, n))), s)))

# Adding again with the kept bit is adding the dependency the first add wrote,
# by `readd_again`, and adding that twice is adding it once, by `add_idem`.
def Laws.add_keep_idem(m, d):
  match m:
    case M.Manifest{+n, +e, +b, +hb, +hbpa, +hbpv, +ds, +ts}:
      Equal.trans(M.Manifest,
        Rend.add(Rend.add(M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}, Rend.readd(ds, d)),
          Rend.readd(List.append(&2, M.Dep,
            Rend.without(ds, M.dep.name(Rend.readd(ds, d))), [Rend.readd(ds, d)]), d)),
        Rend.add(Rend.add(M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}, Rend.readd(ds, d)),
          Rend.readd(ds, d)),
        Rend.add(M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}, Rend.readd(ds, d)),
        Equal.cong(M.Dep, M.Manifest,
          y => Rend.add(Rend.add(M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}, Rend.readd(ds, d)), y),
          Rend.readd(List.append(&2, M.Dep,
            Rend.without(ds, M.dep.name(Rend.readd(ds, d))), [Rend.readd(ds, d)]), d),
          Rend.readd(ds, d),
          readd_again(ds, d)),
        L1.add_idem(M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}, Rend.readd(ds, d)))
