import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A

# LAW: a git section that names no root is the top of the checkout. A
# ledger written before the `root` key existed can only have meant that,
# and a lock already spells it out as ".".
law source_of_absent_root:
  for +pairs: List<&2, T.Kv>
  for e0: {False{} == String.is_empty(M.value(pairs, "git")) : Bool}
  for e1: {True{} == String.is_empty(M.value(pairs, "root")) : Bool}
  {M.source_of(pairs)
    == M.Git{M.value(pairs, "git"), M.value(pairs, "rev"),
      M.value(pairs, "tag"), ".", M.value(pairs, "narHash"),
      M.flag(M.value(pairs, "vendor"))} : M.Source}
