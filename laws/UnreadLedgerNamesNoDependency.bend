import Base
import ../src/ledger/manifest.bend as M

# LAW: and a ledger that did not read names no dependency at all, rather than
# the first one it happened to have parsed before it gave up.
law dep_of_unread_is_blank:
  for why: String
  for name: String
  {M.dep(M.Bad{why}, name) == M.Dep{"", "", "", M.Hub{""}} : M.Dep}
