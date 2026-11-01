# proofs of laws/ParseReadsTheSections.bend
import Base
import ../src/ledger/manifest.bend as M
import ../laws/ParseReadsTheSections.bend as Laws

def Laws.parse_reads_the_sections(_text, _bad, _name, _pairs, sects, e):
  %e : {M.parse.go(_) == M.read(_bad, sects) : M.Read}
  {==}
