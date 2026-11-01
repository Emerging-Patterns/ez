# proofs of laws/DepsSkipsOtherSections.bend
import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../laws/DepsSkipsOtherSections.bend as Laws

def Laws.deps_skips_other_sections(n, ps, ss, e):
  %e : {M.deps.put(_, T.Sect{n, ps}, M.deps(ss)) == M.deps(ss)
    : List<&2, M.Dep>}
  {==}
