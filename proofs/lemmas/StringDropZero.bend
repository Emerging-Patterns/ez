# nothing taken off the front of a string leaves the string
import Base

# LAW: nothing taken off the front of a string leaves the string
law drop_zero_ledger:
  for s: String
  {String.drop(s, 0n) == s : String}

def drop_zero_ledger(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}
