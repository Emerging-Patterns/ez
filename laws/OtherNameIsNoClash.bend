import Base
import ../src/ledger/manifest.bend as M
import ../src/ez/named.bend as Named

# LAW: an entry of another name is not a clash, whatever its source
law clash_skips:
  for m: String
  for h: String
  for en: String
  for s: M.Source
  for t: List<&2, M.Dep>
  for +name: String
  for +url: String
  for ne: {False{} == String.eq(m, name) : Bool}
  {Named.clash(M.Dep{m, h, en, s} <> t, name, url)
    == Named.clash(t, name, url) : Bool}
