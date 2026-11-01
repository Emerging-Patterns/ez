import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A

# LAW: a dependency section with no hash is reported, by its own name, before
# any section after it, unless it names a workspace member, which records
# none. A hash is the `0x` name the import line carries, so any other section
# without one names a package ez cannot resolve.
law missing_finds_first:
  for +n: String
  for +ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  for e0: {True{} == String.starts_with(n, "deps.") : Bool}
  for e1: {True{} == String.is_empty(M.value(ps, "hash")) : Bool}
  for e2: {False{} == M.flag(M.value(ps, "workspace")) : Bool}
  {M.missing(T.Sect{n, ps} <> ss) == n : String}
