import Base
import ../src/ez/target.bend as Tgt

# LAW: `~/…` expands under the home directory
law expand_home:
  for +home: String
  for +rest: String
  {Tgt.expand(home, "~/" ++ rest) == home ++ ("/" ++ rest) : String}
