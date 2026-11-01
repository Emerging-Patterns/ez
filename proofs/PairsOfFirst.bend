# proofs of laws/PairsOfFirst.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../laws/PairsOfFirst.bend as Laws

def Laws.pairs_of_first(name, ps, ss):
  Equal.cong(Bool, List<&2, T.Kv>,
    b => Bool.pick(List<&2, T.Kv>, b, ps, M.pairs_of(ss, name)),
    String.eq(name, name), True{}, Eq.string_eq_self(name))
