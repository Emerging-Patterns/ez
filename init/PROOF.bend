# init: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./plan.bend as IP
import ../lock/plan.bend as P
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# A ledger that is there is the arm with no effect; one that is not is the
# arm that succeeds, against the premise.
def Laws.init_refusal_writes_nothing(w, r):
  match w:
    case IP.World{n, e, led, ig, mn}:
      match led:
        case Some{s}:
          {==}
        case None{}:
          Eq.bit.absurd(&2, {P.writes(IP.plan(IP.World{n, e, None{}, ig, mn}))
            == False{} : Bool}, r)

# A ledger that is there picks the arm that plans nothing.
def Laws.init_keeps_ledger(_name, _entry, _s, _ignore, _main):
  {==}
