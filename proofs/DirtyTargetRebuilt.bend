# proofs of laws/DirtyTargetRebuilt.bend
import Base
import ../src/ez/key.bend as KKey
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../laws/DirtyTargetRebuilt.bend as Laws
import ../laws/ToolCacheReused.bend as L1
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

# LAW: an `and` with a False right half is False
law and_false_tool:
  for u: Bool
  {Bool.and(u, False{}) == False{} : Bool}

def and_false_tool(u):
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a World with no commit reuses nothing
law unrevved_miss:
  for +w: TW.World
  for none: {TP.rev(w) == "" : String}
  {TP.reuse(w) == False{} : Bool}

def unrevved_miss(w, none):
  %Equal.sym(String, TP.rev(w), "", none)
    : {Bool.and(TP.there(w), KKey.reuse(TP.was(w), KKey.Stamp{_, TP.file(w), TW.bend(w)}))
      == False{} : Bool}
  %Equal.sym(Bool, KKey.reuse(TP.was(w), KKey.Stamp{"", TP.file(w), TW.bend(w)}), False{},
    M2.no_rev(TP.was(w), TP.file(w), TW.bend(w)))
    : {Bool.and(TP.there(w), _) == False{} : Bool}
  and_false_tool(TP.there(w))

def Laws.tool_unrevved_builds(w, ok, none):
  L1.tool_builds_on_miss(w, ok, unrevved_miss(w, none))

# LAW: a local path with anything in `git status` is no commit, whatever
# else holds
law dirty_go:
  for ok: Bool
  for same: Bool
  for +head: String
  {TP.local.go(ok, False{}, same, head) == "" : String}

def dirty_go(ok, _same, _head):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.local_rev_dirty(abs, top, head, ok, _status, d):
  %d : {TP.local.go(ok, _, String.eq(top, abs), head) == "" : String}
  dirty_go(ok, String.eq(top, abs), head)

def Laws.local_rev_unchecked(_abs, _top, _head, _status):
  {==}

# LAW: nor one that is not the top of its checkout
law apart_go:
  for ok: Bool
  for clean: Bool
  for +head: String
  {TP.local.go(ok, clean, False{}, head) == "" : String}

def apart_go(ok, clean, _head):
  match ok:
    case True{}:
      match clean:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def Laws.local_rev_elsewhere(_abs, _top, head, ok, status, e):
  %e : {TP.local.go(ok, String.is_empty(status), _, head) == "" : String}
  apart_go(ok, String.is_empty(status), head)
