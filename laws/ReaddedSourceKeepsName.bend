import Base
import ../src/ledger/manifest.bend as M
import ../src/ez/named.bend as Named

# LAW: a ledger that already holds this git source keeps the name it gave it,
# so adding it again replaces that entry rather than adding a second
law had_keeps:
  for n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for fresh: String
  {Named.had(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    fresh) == n : String}
