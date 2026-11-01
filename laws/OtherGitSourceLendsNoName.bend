import Base
import ../src/ledger/manifest.bend as M
import ../src/ez/named.bend as Named

# LAW: an entry from another git source does not lend this one its name
law had_skips_git:
  for n: String
  for h: String
  for en: String
  for u: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for fresh: String
  for ne: {False{} == String.eq(u, url) : Bool}
  {Named.had(M.Dep{n, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, url,
    fresh) == Named.had(t, url, fresh) : String}
