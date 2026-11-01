import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: a section answers a key with the value written for it, the way a table
# does. `manifest.value` is the table lookup and not a second one.
law value_first_in_section:
  for +k: String
  for v: String
  for ps: List<&2, T.Kv>
  {M.value(T.Kv{k, v} <> ps, k) == v : String}
