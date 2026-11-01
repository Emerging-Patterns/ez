# proofs of laws/DepOpensItsSection.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/render.bend as Rend
import ../laws/DepOpensItsSection.bend as Laws

def Laws.dep_opens_its_section(n, h, e, s):
  Eq.starts_append(n, "]\n" ++ Rend.line("hash", h) ++ Rend.source(s) ++ Rend.line("entry", e))
