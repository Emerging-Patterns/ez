# `ez tool install` and `ez tool upgrade` never run the built binary.
import Base
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# LAW: `install` and `upgrade` never start the program, whatever the World
law tool_link_never_runs:
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.launches(TP.plan(w)) == False{} : Bool}
