# ez, run against the repo it is built from. The ledger here names ez's own
# program as its entry, and `ez check` checks it without running it.
import Base
import 0xead4c7939c9eaca8d47da53b4496b731/main.bend as R
import ../src/ez/quiet.bend as Q
import ../src/check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(["bin/ez.bin", "check"])
    Check.eq_str("ez checks the repo's own ledger", Q.chomp(R.text(out)),
      "ok main.bend")

#|ok ez checks the repo's own ledger
