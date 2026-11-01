import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: a git section's vendor bit is its `vendor` key read as `true`, and
# nothing else. This is the bit the allowlist is derived from.
law source_of_vendor:
  for +pairs: List<&2, T.Kv>
  for e: {False{} == String.is_empty(M.value(pairs, "git")) : Bool}
  {M.source.vendor(M.source_of(pairs)) == M.flag(M.value(pairs, "vendor"))
    : Bool}
