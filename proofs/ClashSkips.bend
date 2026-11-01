# proofs of laws/ClashSkips.bend
import Base
import ../src/ez/named.bend as Named
import ../laws/ClashSkips.bend as Laws

def Laws.clash_skips(_m, _h, _en, s, t, name, url, ne):
  %ne : {Named.clash.at(_, s, url, Named.clash(t, name, url))
    == Named.clash(t, name, url) : Bool}
  {==}
