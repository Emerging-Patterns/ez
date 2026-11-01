# proofs of laws/BaseLast.bend
import Base
import ../src/pkg/path.bend as Path
import ../laws/BaseLast.bend as Laws

# LAW: the walk carries a component only until another follows it
law base_last.go:
  for ps: List<&2, String>
  for +h: String
  for +x: String
  {Path.base.go(List.append(&2, String, ps, [x]), h) == x : String}

def base_last.go(ps, _h, x):
  match ps:
    case []:
      {==}
    case +a <> t:
      base_last.go(t, a, x)

def Laws.base_last(ps, x):
  match ps:
    case []:
      {==}
    case +h <> t:
      base_last.go(t, h, x)
