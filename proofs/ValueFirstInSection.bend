# proofs of laws/ValueFirstInSection.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/toml/toml.bend as T
import ../laws/ValueFirstInSection.bend as Laws

# The ledger's lookup is the table's, and the table answers a key it just
# wrote.
def Laws.value_first_in_section(k, v, ps):
  Equal.cong(Bool, String, b => Bool.pick(String, b, v, T.value(ps, k)),
    String.eq(k, k), True{}, Eq.string_eq_self(k))
