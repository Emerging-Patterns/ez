# proofs of laws/GapOfFullPin.bend
import Base
import ../src/add/world.bend as A
import ../src/share/pin.bend as PinPin
import ../laws/GapOfFullPin.bend as Laws

# A pin's two emptiness tests are rewritten to the False each premise gives,
# and what is left is the arm that passes or the reason written out.
def Laws.gap_of_full_pin(n, _e, _b, _url, _rev, _tag, _root, nar, _vend, fr, fn):
  %fr : {PinPin.gap.git(_, String.is_empty(nar), n) == "" : String}
  %fn : {PinPin.gap.git(False{}, _, n) == "" : String}
  {==}
