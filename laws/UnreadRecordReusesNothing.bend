import Base
import ../src/ez/key.bend as KKey

# LAW: a record that did not read, such as one written before the file and
# the bend were recorded, reuses nothing
law key_none_misses:
  for +r: String
  for +f: String
  for +b: String
  for e: {False{} == String.is_empty(r) : Bool}
  {KKey.reuse(KKey.none(), KKey.Stamp{r, f, b}) == False{} : Bool}
