# proofs of laws/VendorBitIsVendorKey.bend
import Base
import ../src/ledger/manifest.bend as M
import ../laws/VendorBitIsVendorKey.bend as Laws

# The `git` key is there, so the source is a git one, and its bit is the
# `vendor` key read by `flag`.
def Laws.source_of_vendor(pairs, e):
  %e : {M.source.vendor(M.source.go(_, M.value(pairs, "git"),
    M.value(pairs, "rev"), M.value(pairs, "tag"),
    M.root.or(M.value(pairs, "root")), M.value(pairs, "narHash"),
    M.flag(M.value(pairs, "vendor")))) == M.flag(M.value(pairs, "vendor"))
    : Bool}
  {==}
