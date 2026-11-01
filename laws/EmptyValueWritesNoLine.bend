import Base
import ../src/ledger/render.bend as Rend

# LAW: a key with no value leaves no trace in the file. An absent tag or entry
# is absent, and never written as an empty string the next read would take for
# a value.
law line_absent:
  for key: String
  {Rend.line(key, "") == "" : String}
