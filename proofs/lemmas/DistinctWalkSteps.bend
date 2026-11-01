# each step of the package walk keeps every resolved hash distinct
import Base
import ../../src/check/eq.bend as Eq
import ../../src/lock/plan.bend as P
import ../../src/lock/lock.bend as L
import ../../src/lock/world.bend as W
import ../../src/add/world.bend as A
import ../../laws/WalkKeepsHashesDistinct.bend as L1
import ../../laws/defs/DistinctPackHashes.bend as D1
import ./LockPlannerFacts.bend as M1

# The walk's hashes, one step at a time, in the shape of its sources above. A
# step resolves a hash only in the arm where `L.has` answered False, so the
# facts it needs are what an `or`, an `any.step` and an `and` that answered
# are made of.

# LAW: the left half of an `or` that answered False
law or_left_lock:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_left_lock(a, _b, e):
  match a:
    case False{}:
      {==}
    case True{}:
      e

# LAW: the negation of a bit that answered False
law not_false:
  for u: Bool
  for e: {u == False{} : Bool}
  {Bool.not(u) == True{} : Bool}

def not_false(u, e):
  match u:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, e)

# LAW: a hash a package list does not have is fresh to it
law has_fresh:
  for +ps: List<&2, L.Pack>
  for +x: String
  for +e: {L.has(ps, x) == False{} : Bool}
  {D1.hash.fresh(x, ps) == True{} : Bool}

def has_fresh(ps, x, e):
  match ps:
    case []:
      {==}
    case +p <> +t:
      M1.and_true(Bool.not(String.eq(x, L.pack.hash(p))), D1.hash.fresh(x, t),
        not_false(String.eq(x, L.pack.hash(p)),
          M1.any_head(String.eq(x, L.pack.hash(p)), _u => L.has(t, x), e)),
        has_fresh(t, x,
          M1.any_rest(String.eq(x, L.pack.hash(p)), _u => L.has(t, x), e)))

# LAW: a package resolved by its verdict is one the walk did not have
law verdict_distinct:
  for +ns: List<&2, L.Name>
  for v: W.Verdict
  for src: L.Src
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {D1.packs.distinct(packs) == True{} : Bool}
  for n: {L.has(packs, hash) == False{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.step.verdict(v, ns, src, hash, rest, packs, asks,
    bad))) == True{} : Bool}

def verdict_distinct(_ns, v, _src, hash, _rest, packs, _asks, _bad, e, n):
  match v:
    case W.No{_why}:
      e
    case W.Ok{_fs, _ss}:
      M1.and_true(D1.hash.fresh(hash, packs), D1.packs.distinct(packs),
        has_fresh(packs, hash, n), e)
    case W.Named{_names}:
      e

# LAW: and one looked up, whether it was answered or not
law look_distinct:
  for +ns: List<&2, L.Name>
  for found: P.Look
  for src: L.Src
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {D1.packs.distinct(packs) == True{} : Bool}
  for n: {L.has(packs, hash) == False{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.step.look(found, ns, src, hash, rest, packs, asks,
    bad))) == True{} : Bool}

def look_distinct(ns, found, src, hash, rest, packs, asks, bad, e, n):
  match found:
    case P.Absent{}:
      e
    case P.Found{v}:
      verdict_distinct(ns, v, src, hash, rest, packs, asks, bad, e, n)

# LAW: and one passed over, or picked because the walk did not have it
law pick_distinct:
  for +ns: List<&2, L.Name>
  for seen: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for +asks: List<&2, String>
  for bad: String
  for e: {D1.packs.distinct(packs) == True{} : Bool}
  for hs: {Bool.or(L.has(packs, hash), L.seen.holds(asks, hash)) == seen : Bool}
  {D1.packs.distinct(P.walk.packs(P.step.pick(seen, orgs, ns, js, hash, rest, packs,
    asks, bad))) == True{} : Bool}

def pick_distinct(ns, seen, orgs, js, hash, rest, packs, asks, bad, e, hs):
  match seen:
    case True{}:
      e
    case False{}:
      look_distinct(ns, P.look(js, hash), L.origin(orgs, hash), hash, rest, packs,
        asks, bad, e,
        or_left_lock(L.has(packs, hash), L.seen.holds(asks, hash), hs))

# LAW: and one step of the walk, whatever the queue held
law pop_distinct:
  for +ns: List<&2, L.Name>
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for queue: List<&2, String>
  for +packs: List<&2, L.Pack>
  for +asks: List<&2, String>
  for bad: String
  for e: {D1.packs.distinct(packs) == True{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.step.pop(orgs, ns, js, queue, packs, asks, bad)))
    == True{} : Bool}

def pop_distinct(ns, orgs, js, queue, packs, asks, bad, e):
  match queue:
    case []:
      e
    case +h <> t:
      pick_distinct(ns, Bool.or(L.has(packs, h), L.seen.holds(asks, h)), orgs, js,
        h, t, packs, asks, bad, e, {==})

# LAW: one step keeps every resolved hash distinct
law step_distinct:
  for +ns: List<&2, L.Name>
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for wk: P.Walk
  for e: {D1.packs.distinct(P.walk.packs(wk)) == True{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.walk.step(orgs, ns, js, wk))) == True{} : Bool}

def step_distinct(ns, orgs, js, wk, e):
  match wk:
    case P.Walk{queue, packs, asks, bad}:
      pop_distinct(ns, orgs, js, queue, packs, asks, bad, e)

# LAW: a walk that ran out of fuel keeps the packages it had
law out_distinct:
  for done: Bool
  for wk: P.Walk
  for e: {D1.packs.distinct(P.walk.packs(wk)) == True{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.walk.out(done, wk))) == True{} : Bool}

def out_distinct(done, wk, e):
  match done:
    case True{}:
      e
    case False{}:
      match wk:
        case P.Walk{_queue, _packs, _asks, _bad}:
          e

# LAW: a walk that is done is what it was, and one that is not goes on
law more_distinct:
  for +ns: List<&2, L.Name>
  for done: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for f: Nat
  for +wk: P.Walk
  for e: {D1.packs.distinct(P.walk.packs(wk)) == True{} : Bool}
  for ih: {D1.packs.distinct(P.walk.packs(P.walk(f, orgs, ns, js,
    P.walk.step(orgs, ns, js, wk)))) == True{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.walk.more(done, wk,
    now => P.walk(f, orgs, ns, js, P.walk.step(orgs, ns, js, now))))) == True{} : Bool}

def more_distinct(_ns, done, _orgs, _js, _f, _wk, e, ih):
  match done:
    case True{}:
      e
    case False{}:
      ih

def L1.walk_keeps_hashes_distinct(fuel, orgs, ns, js, wk, e):
  match fuel:
    case 0n:
      out_distinct(P.walk.done(wk), wk, e)
    case 1n+f:
      more_distinct(ns, P.walk.done(wk), orgs, js, f, wk, e,
        L1.walk_keeps_hashes_distinct(f, orgs, ns, js, P.walk.step(orgs, ns, js, wk),
          step_distinct(ns, orgs, js, wk, e)))
