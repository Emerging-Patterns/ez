# `ez tool run` exits with the built program's status; any failure before the
# program runs exits 1.
import Base
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# ---------------------------------------------------------------------------
# laws/ToolRunExitsWithProgram.bend and laws/ToolLinkNeverRuns.bend: the
# program

# LAW: `ez tool run` that does not refuse ends by starting the program with
# the words it was given, as the last thing, so its status is the command's
law tool_run_exits_with_program:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.exit(TP.plan(w)) == TP.Exits{TP.out(w), args} : TP.Exit}

# LAW: a tool command that refuses exits 1 and starts nothing
law tool_refusal_exits_one:
  for +w: TW.World
  for r: {TP.refuses(w) == True{} : Bool}
  {TP.exit(TP.plan(w)) == TP.Refusal{} : TP.Exit}
