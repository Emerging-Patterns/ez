import Base
import ../src/pkg/path.bend as Path

# LAW: skipping a component leaves the walk as it was
law skip_id:
  for w: Path.Walk
  {Path.norm.go(w, Path.CSkip{}) == w : Path.Walk}
