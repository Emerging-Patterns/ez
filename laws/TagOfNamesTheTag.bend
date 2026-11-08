import Base
import ../src/ledger/manifest.bend as M

# LAW: and the tag it was asked for is the tag its git section wrote
law tag_of_names_the_tag:
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
  for rev: String
  for +tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  {M.tag_of(M.Good{M.Manifest{mn, me, mb, mh, mhpa, mhpv,
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, ts}}, n) == tag
    : String}
