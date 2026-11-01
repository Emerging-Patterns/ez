import Base
import ../src/pkg/path.bend as Path

# whether a half-finished normalisation began at the root
def walk.abs(state: Path.Walk) -> Bool:
  Path.Walk{abs, out} = state
  abs

# LAW: a normalisation carries the root flag it started with, whatever the
# components did to what it kept.
law walk_keeps_root:
  for cs: List<&2, String>
  for +w: Path.Walk
  {walk.abs(Path.norm.walk(cs, w)) == walk.abs(w) : Bool}
