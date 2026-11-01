import Base
import ../src/ledger/manifest.bend as M
import ../src/ez/named.bend as Named

# LAW: nor does a hub entry, which has no git source to be
law had_skips_hub:
  for n: String
  for h: String
  for en: String
  for +url: String
  for t: List<&2, M.Dep>
  for fresh: String
  {Named.had(M.Dep{n, h, en, M.Hub{""}} <> t, url, fresh)
    == Named.had(t, url, fresh) : String}
