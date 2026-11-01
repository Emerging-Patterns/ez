# a path that every path starting with it extends
import Base

# a path every path that starts with it extends. Law vocabulary: ez never
# calls it.
def prefix(ps: List<&2, String>, ds: List<&2, String>) -> Bool:
  match ps:
    case []:
      True{}
    case +ph <> pt:
      match ds:
        case []:
          False{}
        case +dh <> dt:
          Bool.and(String.eq(ph, dh), prefix(pt, dt))
