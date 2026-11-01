# proofs of laws/DepsTakesDepSections.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../laws/DepsTakesDepSections.bend as Laws

# The section's name opens with the prefix because it was built from it.
def Laws.deps_takes_dep_sections(name, ps, ss):
  Equal.cong(Bool, List<&2, M.Dep>,
    b => M.deps.put(b, T.Sect{String.append("deps.", name), ps}, M.deps(ss)),
    String.starts_with(String.append("deps.", name), "deps."), True{},
    Eq.starts_append("deps.", name))
