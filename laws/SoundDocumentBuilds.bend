import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A

# The rest of the ledger: the reading of a parsed document into a model, and
# the writing of that model back out. A ledger is a file a person edits, so
# every one of these is a claim about what ez will do with what they wrote.

# whether a document was read into a ledger rather than into a reason
def is_good(read: M.Read) -> Bool:
  match read:
    case M.Bad{why}:
      False{}
    case M.Good{m}:
      True{}

# LAW: once a document is known to be sound, building it cannot fail. Every
# refusal ez makes about a ledger is made by `problem`, and this says `build`
# adds none of its own.
law build_is_good:
  for +ss: List<&2, T.Sect>
  {is_good(M.build(ss)) == True{} : Bool}
