# proofs of laws/MissingFindsFirst.bend
import Base
import ../src/ledger/manifest.bend as M
import ../laws/MissingFindsFirst.bend as Laws

def Laws.missing_finds_first(n, ps, ss, e0, e1, e2):
  %e0 : {M.missing.at(Bool.and(_, Bool.and(Bool.not(M.flag(M.value(ps, "workspace"))),
    String.is_empty(M.value(ps, "hash")))), n, M.missing(ss)) == n : String}
  %e2 : {M.missing.at(Bool.and(True{}, Bool.and(Bool.not(_), String.is_empty(M.value(ps, "hash")))), n,
    M.missing(ss)) == n : String}
  %e1 : {M.missing.at(Bool.and(True{}, Bool.and(True{}, _)), n, M.missing(ss)) == n : String}
  {==}
