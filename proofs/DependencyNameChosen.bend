# proofs of laws/DependencyNameChosen.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/ez/named.bend as Named
import ../laws/DependencyNameChosen.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/BareKeyDots.bend as M2
import ./lemmas/LockPlannerFacts.bend as M3
import ./lemmas/PlanEffectFacts.bend as M4
import ./lemmas/PlannerStages.bend as M5

def Laws.add_records_named(w, ok):
  Equal.cong(M.Dep, String, d => M.dep.name(d), AP.added(w),
    AP.dep.of(M3.wh(AP.walked(w)), M4.wr(AP.walked(w)), w), M1.added_ok(w, ok))

law named_walk:
  for k: K.Walked
  for +w: A.World
  for e: {False{} == String.is_empty(AP.why(w)) : Bool}
  {M3.win(AP.outcome.walk(k, w)) == False{} : Bool}

def named_walk(k, w, e):
  match k:
    case K.Walked{+h, +r, _fs, _ss}:
      %e : {M3.win(AP.outcome.name(_,
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
  {M3.win(AP.outcome.entry(g, k, w)) == False{} : Bool}

def named_loses(g, k, w, e):
  match g:
    case None{}:
      {==}
    case Some{_t}:
      named_walk(k, w, e)

def Laws.add_refuses_named(w, why):
  M3.lose_v(AP.decide(w), w, named_loses(M3.got(w), AP.walked(w), w, why))

# The key is the one `dep.of` records, whatever the World.
def Laws.add_named_key(_w):
  {==}

# LAW: a pick between two texts that are not empty is not empty
law pick_full:
  for c: Bool
  for +x: String
  for +y: String
  for ex: {False{} == String.is_empty(x) : Bool}
  for ey: {False{} == String.is_empty(y) : Bool}
  {False{} == String.is_empty(Bool.pick(String, c, x, y)) : Bool}

def pick_full(c, _x, _y, ex, ey):
  match c:
    case True{}:
      ex
    case False{}:
      ey

# LAW: a refusal the ledger decides stops the add
law hearly_false:
  for b: Bool
  for +why: String
  for +w: A.World
  for e: {False{} == b : Bool}
  {M5.hstops(H.decide.early(b, why, w)) == True{} : Bool}

def hearly_false(b, why, w, e):
  match b:
    case True{}:
      Eq.bit.absurd(&2, {M5.hstops(H.decide.early(True{}, why, w)) == True{} : Bool}, e)
    case False{}:
      {==}

def Laws.add_named_refuses_clash(w, why):
  M5.hstops_refuses(H.decide(w), w,
    M5.hread_stops(A.read(w), w,
      hearly_false(String.is_empty(H.early(w)), H.early(w), w,
        pick_full(Bool.or(String.is_empty(A.ref(w)), String.is_empty(A.entry.arg(w))),
          Named.hub.why(A.deps(w), H.key(w), H.part(w), A.rename(w)),
          "ez: " ++ A.target(w) ++ " pins its version; the word after it is the entry, " ++
            "and there is only one", why, {==}))))

# named: a walk from the end of a text has passed a slash once it has passed
# the one in front of `n`, and nothing to its left changes that. The name laws
# rewrite the one `String.eq` each branch turns on.

# LAW: past the slash in front of a slashless `n`, the walk has seen a slash
# and kept `n`, whatever is to the left of it
law last_after:
  for p: String
  for +n: String
  for e: {Named.Seen{False{}, n} == Named.last(n) : Named.Seen}
  {Named.last(p ++ ("/" ++ n)) == Named.Seen{True{}, n} : Named.Seen}

def last_after(p, n, e):
  match p:
    case SNil{}:
      %e : {Named.last.step('/', _) == Named.Seen{True{}, n} : Named.Seen}
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Named.Seen, Named.last(t ++ ("/" ++ n)), Named.Seen{True{}, n},
        last_after(t, n, e)) :
        {Named.last.step(h, _) == Named.Seen{True{}, n} : Named.Seen}
      {==}

def Laws.leaf_is_last(p, n, e):
  Equal.cong(Named.Seen, String, Named.leaf.of,
    Named.last(p ++ ("/" ++ n)), Named.Seen{True{}, n}, last_after(p, n, e))

def Laws.own_package(pkg, fresh, e):
  %e : {Bool.pick(String, _, pkg, fresh) == pkg : String}
  {==}

def Laws.own_invalid(pkg, fresh, e):
  %e : {Bool.pick(String, _, pkg, fresh) == fresh : String}
  {==}

def Laws.name_keeps(n, _h, _en, url, _rev, _tag, _root, _nar, _vend, t, pkg, fresh):
  %Equal.sym(Bool, String.eq(url, url), True{}, Eq.string_eq_self(url)) :
    {Named.had.at(_, n, Named.had(t, url, Named.own(pkg, fresh))) == n : String}
  {==}

def Laws.clash_same(n, _h, _en, url, rev, tag, root, nar, vend, t):
  %Equal.sym(Bool, String.eq(n, n), True{}, Eq.string_eq_self(n)) :
    {Named.clash.at(_, M.Git{url, rev, tag, root, nar, vend}, url,
      Named.clash(t, n, url)) == False{} : Bool}
  %Equal.sym(Bool, String.eq(url, url), True{}, Eq.string_eq_self(url)) :
    {Bool.not(_) == False{} : Bool}
  {==}

# LAW: a name held first by another git source clashes
law clash_first:
  for +n: String
  for h: String
  for en: String
  for u: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ne: {False{} == String.eq(u, url) : Bool}
  {Named.clash(M.Dep{n, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, n,
    url) == True{} : Bool}

def clash_first(n, _h, _en, u, url, rev, tag, root, nar, vend, t, ne):
  %Equal.sym(Bool, String.eq(n, n), True{}, Eq.string_eq_self(n)) :
    {Named.clash.at(_, M.Git{u, rev, tag, root, nar, vend}, url,
      Named.clash(t, n, url)) == True{} : Bool}
  %ne : {Bool.not(_) == True{} : Bool}
  {==}

def Laws.clash_other(n, h, en, u, url, rev, tag, root, nar, vend, t, ne):
  clash_first(n, h, en, u, url, rev, tag, root, nar, vend, t, ne)

def Laws.clash_hub(n, _h, _en, url, t):
  %Equal.sym(Bool, String.eq(n, n), True{}, Eq.string_eq_self(n)) :
    {Named.clash.at(_, M.Hub{""}, url, Named.clash(t, n, url)) == True{} : Bool}
  {==}

# LAW: a given `--rename` is the name
law as_rename:
  for ds: List<&2, M.Dep>
  for +url: String
  for +rename: String
  for +pkg: String
  for +fresh: String
  for e: {False{} == String.is_empty(rename) : Bool}
  {Named.as(ds, url, rename, pkg, fresh) == rename : String}

def as_rename(ds, url, rename, pkg, fresh, e):
  %e : {Bool.pick(String, _, Named.name(ds, url, pkg, fresh), rename) == rename
    : String}
  {==}

def Laws.rename_wins(ds, url, rename, pkg, fresh, e):
  as_rename(ds, url, rename, pkg, fresh, e)

def Laws.rename_dotted(a, b):
  %M4.nonempty_app(a, '.', b) :
    {Bool.or(_, Named.bare(a ++ ("." ++ b))) == False{} : Bool}
  M2.bare_dot(a, b)

# LAW: a second, different, non-empty name for a recorded source is moved
law moved_of:
  for +n: String
  for +rename: String
  for er: {False{} == String.is_empty(rename) : Bool}
  for en0: {False{} == String.is_empty(n) : Bool}
  for nr: {False{} == String.eq(n, rename) : Bool}
  {Named.moved.of(n, rename) == True{} : Bool}

def moved_of(n, rename, er, en0, nr):
  %er : {Bool.and(Bool.not(_), Bool.and(Bool.not(String.is_empty(n)),
    Bool.not(String.eq(n, rename)))) == True{} : Bool}
  %en0 : {Bool.and(Bool.not(_), Bool.not(String.eq(n, rename))) == True{}
    : Bool}
  %nr : {Bool.not(_) == True{} : Bool}
  {==}

# The ledger's name for the source is `n` (`had_keeps`), and the premises
# settle the three tests on it.
def Laws.rename_moved(n, h, en, url, rev, tag, root, nar, vend, t, rename, er, en0, nr):
  Equal.trans(Bool,
    Named.moved(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
      rename),
    Named.moved.of(n, rename),
    True{},
    Equal.cong(String, Bool, o => Named.moved.of(o, rename),
      Named.had(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
        ""),
      n,
      M4.had_first(n, h, en, url, rev, tag, root, nar, vend, t, "")),
    moved_of(n, rename, er, en0, nr))

# `--rename` is the name (`rename_wins`), and that name is held by another
# source (`clash_other`).
def Laws.rename_clash(r, h, en, u, url, rev, tag, root, nar, vend, t, pkg, fresh, ne, er):
  Equal.trans(Bool,
    Named.clash(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t,
      Named.as(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, url, r,
        pkg, fresh), url),
    Named.clash(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, r,
      url),
    True{},
    Equal.cong(String, Bool,
      o => Named.clash(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t,
        o, url),
      Named.as(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, url, r,
        pkg, fresh),
      r,
      as_rename(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t,
        url, r, pkg, fresh, er)),
    clash_first(r, h, en, u, url, rev, tag, root, nar, vend, t, ne))

def Laws.hub_rename_wins(ds, part, rename, e):
  %e : {Bool.pick(String, _, Bool.pick(String, String.is_empty(Named.hub.had(ds, part)), part,
    Named.hub.had(ds, part)), rename) == rename : String}
  {==}

def Laws.hub_key_keeps(n, _h, _en, nv, t, e):
  %Equal.sym(Bool, String.eq(Named.hub.part(nv), Named.hub.part(nv)), True{},
    Eq.string_eq_self(Named.hub.part(nv)))
    : {Bool.pick(String, True{}, Bool.pick(String,
      String.is_empty(Named.had.at(_, n, Named.hub.had(t, Named.hub.part(nv)))),
      Named.hub.part(nv), Named.had.at(_, n, Named.hub.had(t, Named.hub.part(nv)))), "")
      == n : String}
  %e : {Bool.pick(String, _, Named.hub.part(nv), n) == n : String}
  {==}

def Laws.hub_key_fresh(_part):
  {==}

def Laws.hub_clash_git(k, _h, _en, _url, _rev, _tag, _root, _nar, _vend, t, part):
  %Equal.sym(Bool, String.eq(k, k), True{}, Eq.string_eq_self(k))
    : {Named.hub.clash.at(_, M.Git{_url, _rev, _tag, _root, _nar, _vend}, part,
      Named.hub.clash(t, k, part)) == True{} : Bool}
  {==}
