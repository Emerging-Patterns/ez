# check/argv: a test server's command line. `IO.args()` answers a `&1` list,
# which can be read once, with the program's own name first; the servers read
# their arguments more than once, so they take a `&2` copy of the ones after
# the name. Shared by check/framing.bend and check/oracle.bend.
import Base

# a &1 list copied into a &2 one
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

# the arguments after the program's own name. Since bend 2.0.32 `IO.args()`
# starts with the program as it was invoked, as C's argv does.
def args(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_h, t}:
      copy(t)
