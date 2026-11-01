# the names files a lock or a fetch lays under BEND_LIB
import Base
import ../../src/lock/plan.bend as P
import ../../src/lock/lock.bend as L
import ../../src/add/world.bend as A
import ../../src/ez/named.bend as Named

# ---------------------------------------------------------------------------
# Named hub imports (EZ-HUB). A `<name>@<version>` import is a hub package:
# the lock reads it by its name, resolves the name by a table of names, walks
# the package the table gives it, and records the pair under `[names]`. The
# table is the names ez.toml records, each with the hash beside it, first,
# then those the answers resolve: the lock being rewritten's, then the hub's.
# A name is put to the hub only when nothing before it resolves it, and a
# lock that is made lays, for every name it records, the file bend reads the
# name's hash from.

# the names files a list of effects lays, in order. Law vocabulary.
def names.laid(es: List<&2, P.Effect>) -> List<&2, L.Name>:
  match es:
    case []:
      []
    case e <> t:
      match e:
        case P.Name{nv, hash}:
          L.Name{nv, hash} <> names.laid(t)
        case _:
          names.laid(t)
