import Base
import ../src/ez/named.bend as Named

# LAW: a name with a dot in it, like `next.js`, is not a bare key, since
# `[deps.next.js]` would be a table inside a table
law bare_no_dot:
  for +a: String
  for +b: String
  {Named.bare(a ++ ("." ++ b)) == False{} : Bool}
