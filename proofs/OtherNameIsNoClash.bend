# proofs of laws/OtherNameIsNoClash.bend
import Base
import ../src/ez/named.bend as Named
import ../laws/OtherNameIsNoClash.bend as Laws

def Laws.clash_skips(_m, _h, _en, s, t, name, url, ne):
  %ne : {Named.clash.at(_, s, url, Named.clash(t, name, url))
    == Named.clash(t, name, url) : Bool}
  {==}
