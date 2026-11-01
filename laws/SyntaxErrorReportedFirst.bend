import Base
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A

# LAW: a syntax error is reported before a missing hash. A section that did
# not parse cannot be judged for what it holds.
law problem_syntax_first:
  for +bad: String
  for +miss: String
  for e: {False{} == String.is_empty(bad) : Bool}
  {M.problem(bad, miss) == bad : String}
