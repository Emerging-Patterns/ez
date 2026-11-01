import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: so a git source with no tag writes the four keys it does have and
# nothing where the tag would be.
law source_omits_absent_tag:
  for url: String
  for rev: String
  for root: String
  for nar: String
  {Rend.source(M.Git{url, rev, "", root, nar, False{}})
    == Rend.line("git", url) ++ Rend.line("rev", rev) ++ Rend.line("root", root)
      ++ Rend.line("narHash", nar) ++ Rend.line.bare("vendor", "") : String}
