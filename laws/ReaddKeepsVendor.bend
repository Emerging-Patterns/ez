import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: a dependency added again keeps the `vendor = true` the ledger already
# gave it. `ez add` has no way to say it, so dropping it would drop the tree
# from the allowlist without anyone having asked.
law readd_keeps_vendor:
  for ds: List<&2, M.Dep>
  for +n: String
  for h: String
  for en: String
  for url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for v: Bool
  for e: {M.source.vendor(M.source.dep(M.find(ds, n))) == True{} : Bool}
  {M.source.vendor(M.source.dep(Rend.readd(ds,
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, v}}))) == True{} : Bool}
