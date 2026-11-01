# proofs of laws/GapOfNarlessPin.bend
import Base
import ../src/share/pin.bend as PinPin
import ../laws/GapOfNarlessPin.bend as Laws

def Laws.gap_of_narless_pin(n, _e, _b, _url, _rev, _tag, _root, _vend, fr):
  %fr : {PinPin.gap.git(_, True{}, n) == "ez: tools." ++ n ++
    " has no narHash; run `ez lock --upgrade --package " ++ n ++ "` to pin it"
    : String}
  {==}
