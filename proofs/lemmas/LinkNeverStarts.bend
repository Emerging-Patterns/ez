# a linking act never starts the program, whatever the verdict
import Base
import ../../src/check/eq.bend as Eq
import ../../src/lock/plan.bend as P
import ../../src/tool/world.bend as TW
import ../../src/tool/plan.bend as TP

# LAW: a linking act never starts the program
law never_a:
  for a: TW.Act
  for +w: TW.World
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.launches(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(a, w), P.Success{}}) == False{}
    : Bool}

def never_a(a, w, l):
  match a:
    case TW.Run{args}:
      Eq.bit.absurd(&2, {TP.launches(TP.Plan{TP.lay(w), TP.make(w),
        TP.finish.of(TW.Run{args}, w), P.Success{}}) == False{} : Bool}, l)
    case TW.Install{}:
      {==}
    case TW.Upgrade{}:
      {==}

# LAW: whatever the verdict
law never:
  for v: TP.Verdict
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.launches(TP.plan.v(v, w)) == False{} : Bool}

def never(v, w, a, act, l):
  match v:
    case TP.Go{}:
      %Equal.sym(TW.Act, TW.act(w), a, act)
        : {TP.launches(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(_, w), P.Success{}})
          == False{} : Bool}
      never_a(a, w, l)
    case TP.Pending{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}
