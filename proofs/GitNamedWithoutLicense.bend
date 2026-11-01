# proofs of laws/GitNamedWithoutLicense.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../laws/GitNamedWithoutLicense.bend as Laws

def Laws.git_named_without_license(hash, manifest, ss, unnamed):
  %unnamed : {W.git.rule(_, hash, manifest, ss)
    == W.git.body(List.is_empty(&2, K.Item, K.bare(L.manifest.files(String.lines(manifest)))),
      hash, K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))),
      K.bare.srcs(L.manifest.files(String.lines(manifest)), ss)) : W.Verdict}
  {==}
