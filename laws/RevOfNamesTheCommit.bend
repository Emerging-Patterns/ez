import Base
import ../src/ledger/manifest.bend as M

# LAW: the commit a ledger pins a dependency to is the commit its git section
# wrote. This and the law under it are what `ez lock` and `ez doctor` read,
# and they reach through the lookup, the source and the accessor at once.
law rev_of_names_the_commit:
  for mn: String
  for me: String
  for mb: String
  for mh: String
  for mhpa: String
  for mhpv: String
  for +n: String
  for h: String
  for en: String
  for url: String
  for +rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  {M.rev_of(M.Good{M.Manifest{mn, me, mb, mh, mhpa, mhpv,
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, ts}}, n) == rev
    : String}
