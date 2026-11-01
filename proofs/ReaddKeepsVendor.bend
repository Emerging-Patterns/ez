# proofs of laws/ReaddKeepsVendor.bend
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../laws/ReaddKeepsVendor.bend as Laws

# The ledger's bit is true, so the source is marked vendored, and a git
# source marked vendored says so.
def Laws.readd_keeps_vendor(ds, n, h, en, url, rev, tag, root, nar, v, e):
  %Equal.sym(Bool, M.source.vendor(M.source.dep(M.find(ds, n))), True{}, e)
    : {M.source.vendor(M.source.dep(M.Dep{n, h, en,
      Rend.revend(_, M.Git{url, rev, tag, root, nar, v})})) == True{} : Bool}
  {==}
