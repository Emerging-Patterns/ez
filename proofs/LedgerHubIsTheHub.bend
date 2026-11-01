# proofs of laws/LedgerHubIsTheHub.bend
import Base
import ../laws/LedgerHubIsTheHub.bend as Laws

def Laws.hub_of_names_the_hub(_n, _e, _b, hb, _hbpa, _hbpv, _ds, _ts, f):
  %f : {Bool.pick(String, _, "https://hub.bend-lang.com", hb) == hb : String}
  {==}
