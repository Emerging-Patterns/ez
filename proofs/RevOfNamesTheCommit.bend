# proofs of laws/RevOfNamesTheCommit.bend
import Base
import ../src/ledger/manifest.bend as M
import ../laws/LookupFindsFirstDependency.bend as L1
import ../laws/RevOfNamesTheCommit.bend as Laws
import ./lemmas/FirstFound.bend as M1

def Laws.rev_of_names_the_commit(_mn, _me, _mb, _mh, _mhpa, _mhpv, n, h, en, url, rev, tag, root, nar, vend, t, _ts):
  Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)),
    M.find(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, n),
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}},
    L1.find_first(n, h, en, M.Git{url, rev, tag, root, nar, vend}, t))
