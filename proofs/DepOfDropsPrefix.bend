# proofs of laws/DepOfDropsPrefix.bend
import Base
import ../laws/DepOfDropsPrefix.bend as Laws
import ./lemmas/StringDropZero.bend as M1

# `deps.` is five literal characters, so the drop steps through all five and
# what is left is the name with nothing taken off it.
def Laws.dep_of_drops_prefix(name, _pairs):
  M1.drop_zero_ledger(name)
