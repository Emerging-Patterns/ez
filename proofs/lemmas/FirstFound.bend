# a lookup finds the first entry that matches
import Base
import ../../src/check/eq.bend as Eq
import ../../src/ledger/manifest.bend as M
import ../../laws/LookupFindsFirstDependency.bend as L1

def L1.find_first(n, h, en, s, t):
  Equal.cong(Bool, M.Dep,
    b => M.find.pick(b, M.Dep{n, h, en, s}, M.find(t, n)),
    String.eq(n, n), True{}, Eq.string_eq_self(n))
