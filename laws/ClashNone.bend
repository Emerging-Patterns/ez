import Base
import ../src/ez/named.bend as Named

# LAW: an empty ledger clashes with no name
law clash_none:
  for name: String
  for url: String
  {Named.clash([], name, url) == False{} : Bool}
