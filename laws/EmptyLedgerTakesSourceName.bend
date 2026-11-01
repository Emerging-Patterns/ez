import Base
import ../src/ez/named.bend as Named

# LAW: a ledger that holds no dependency takes the name the source gives
# itself
law had_fresh:
  for url: String
  for fresh: String
  {Named.had([], url, fresh) == fresh : String}
