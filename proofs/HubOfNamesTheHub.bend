# proofs of laws/HubOfNamesTheHub.bend
import Base
import ../laws/HubOfNamesTheHub.bend as Laws

def Laws.hub_of_names_the_hub(_n, _e, _b, hb, _hbpa, _hbpv, _ds, _ts, f):
  %f : {Bool.pick(String, _, "https://hub.bend-lang.com", hb) == hb : String}
  {==}
