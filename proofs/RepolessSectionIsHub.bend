# proofs of laws/RepolessSectionIsHub.bend
import Base
import ../src/ledger/manifest.bend as M
import ../laws/RepolessSectionIsHub.bend as Laws

def Laws.source_of_hub(pairs, e):
  %e : {M.source.go(_, M.value(pairs, "git"), M.value(pairs, "rev"),
    M.value(pairs, "tag"), M.root.or(M.value(pairs, "root")),
    M.value(pairs, "narHash"), M.flag(M.value(pairs, "vendor")))
    == M.Hub{""} : M.Source}
  {==}
