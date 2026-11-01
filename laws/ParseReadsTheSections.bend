import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: the ledger is read out of the sections the parse found and the first
# syntax error it found, and out of nothing else -- not out of the text again.
law parse_reads_the_sections:
  for +text: String
  for bad: String
  for name: String
  for pairs: List<&2, T.Kv>
  for sects: List<&2, T.Sect>
  for e: {T.Toml{bad, name, pairs, sects} == T.parse(text) : T.Toml}
  {M.parse(text) == M.read(bad, sects) : M.Read}
