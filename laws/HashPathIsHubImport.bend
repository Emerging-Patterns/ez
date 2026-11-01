import Base
import ../src/pkg/pkg.bend as K

# LAW: a `0x` name followed by a path is a hub import, whatever the
# hash and whatever the path. This is the one `is_hub` answers True
# for, and it is the one the walk does not follow.
law hub_named:
  for +h: String
  for +rest: String
  {K.is_hub(("0x" ++ h) ++ ("/" ++ rest)) == True{} : Bool}
