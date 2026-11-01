# proofs of laws/ToolCacheReused.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ez/key.bend as KKey
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../laws/ToolCacheReused.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1

# key: the hypothesis rewrites one comparison to False, and what is left is an
# `and` ending in False behind the comparisons it did not name. Those are
# open, so the lemmas below take them apart one bit at a time.

# LAW: an `and` whose last half is False is False
law and_false1:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def and_false1(x):
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# LAW: and so is one with two open bits before the False
law and_false2:
  for x: Bool
  for y: Bool
  {Bool.and(x, Bool.and(y, False{})) == False{} : Bool}

def and_false2(x, y):
  match x:
    case False{}:
      {==}
    case True{}:
      and_false1(y)

# LAW: and one with three
law and_false3:
  for x: Bool
  for y: Bool
  for z: Bool
  {Bool.and(x, Bool.and(y, Bool.and(z, False{}))) == False{} : Bool}

def and_false3(x, y, z):
  match x:
    case False{}:
      {==}
    case True{}:
      and_false2(y, z)

def Laws.key_rev_differs(_r0, f0, b0, r1, f1, b1, e):
  %e : {Bool.and(Bool.not(String.is_empty(r1)),
    Bool.and(_, Bool.and(String.eq(f0, f1), String.eq(b0, b1)))) == False{}
    : Bool}
  and_false1(Bool.not(String.is_empty(r1)))

def Laws.key_file_differs(r0, _f0, b0, r1, _f1, b1, e):
  %e : {Bool.and(Bool.not(String.is_empty(r1)),
    Bool.and(String.eq(r0, r1), Bool.and(_, String.eq(b0, b1)))) == False{}
    : Bool}
  and_false2(Bool.not(String.is_empty(r1)), String.eq(r0, r1))

def Laws.key_bend_differs(r0, f0, _b0, r1, f1, _b1, e):
  %e : {Bool.and(Bool.not(String.is_empty(r1)),
    Bool.and(String.eq(r0, r1), Bool.and(String.eq(f0, f1), _))) == False{}
    : Bool}
  and_false3(Bool.not(String.is_empty(r1)), String.eq(r0, r1), String.eq(f0, f1))

# the empty commit computes, and the `and` stops at it whatever was recorded
def Laws.key_no_rev(was, _f, _b):
  match was:
    case KKey.Stamp{_r0, _f0, _b0}:
      {==}

# the commit is not empty, and each field equals itself
def Laws.key_same_reuses(r, f, b, e):
  %e : {Bool.and(Bool.not(_),
    Bool.and(String.eq(r, r), Bool.and(String.eq(f, f), String.eq(b, b))))
    == True{} : Bool}
  %Equal.sym(Bool, String.eq(r, r), True{}, Eq.string_eq_self(r)) :
    {Bool.and(_, Bool.and(String.eq(f, f), String.eq(b, b))) == True{} : Bool}
  %Equal.sym(Bool, String.eq(f, f), True{}, Eq.string_eq_self(f)) :
    {Bool.and(_, String.eq(b, b)) == True{} : Bool}
  Eq.string_eq_self(b)

def Laws.checkout_differs(_was, now, e):
  %e : {Bool.and(Bool.not(String.is_empty(now)), _) == False{} : Bool}
  and_false1(Bool.not(String.is_empty(now)))

def Laws.checkout_same(r, e):
  %e : {Bool.and(Bool.not(_), String.eq(r, r)) == True{} : Bool}
  Eq.string_eq_self(r)

# ---------------------------------------------------------------------------
# laws/ToolCacheReused.bend and laws/DirtyTargetRebuilt.bend: built or reused

# LAW: what `made` builds turns on the record alone
law reuse_made:
  for +w: TW.World
  for hit: {TP.reuse(w) == True{} : Bool}
  {TP.builds(TP.made(w)) == False{} : Bool}

def reuse_made(w, hit):
  %Equal.sym(Bool, TP.reuse(w), True{}, hit) : {TP.makes(TP.make.of(_, w)) == False{} : Bool}
  {==}

def Laws.tool_reuses_record(w, ok, hit):
  Equal.trans(Bool, TP.builds(TP.plan(w)), TP.builds(TP.made(w)), False{},
    Equal.cong(TP.Plan, Bool, pl => TP.builds(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
    reuse_made(w, hit))
