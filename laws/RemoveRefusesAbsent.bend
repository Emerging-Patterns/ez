import Base
import ../src/ledger/manifest.bend as M
import ../src/remove/plan.bend as RP

# LAW: a name the ledger does not have is refused, as `cargo remove` refuses
# it, so removing it writes nothing
law remove_refuses_absent:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for good: {M.Good{m} == M.parse(s) : M.Read}
  for no: {False{} == RP.named(RP.deps.of(m), name) : Bool}
  {RP.refuses(RP.World{name, Some{s}, ignore}) == True{} : Bool}
