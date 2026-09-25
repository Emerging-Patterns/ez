# ez, run against the repo it is built from. The ledger here names a library
# entry, so this is also the "no main to run" case: bend checks the file clean
# and then exits 1 from the emit, and ez has to read that as a pass.
import Base
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(["bin/ez.bin", "check"])
    Check.eq_str("ez checks the repo's own ledger", Q.chomp(R.text(out)),
      "ok ledger/manifest.bend")

#|ok ez checks the repo's own ledger
