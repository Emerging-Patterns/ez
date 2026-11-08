# proofs of laws/UpgradeNamedWithoutReadme.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/up.bend as Up
import ../laws/UpgradeNamedWithoutReadme.bend as Laws

def Laws.upgrade_named_without_readme(pin, manifest, walked, readmeless):
  %walked : {Up.hash.kept.pick(_, pin, Up.hash.of(manifest), manifest)
    == Up.hash.of(K.manifest.lines(K.readmeless(L.manifest.files(String.lines(manifest)))))
    : String}
  %readmeless : {Up.hash.kept.old(_, pin,
      Up.hash.of(K.manifest.lines(K.readmeless(L.manifest.files(String.lines(manifest))))),
      Up.hash.of(manifest), L.manifest.files(String.lines(manifest)))
    == Up.hash.of(K.manifest.lines(K.readmeless(L.manifest.files(String.lines(manifest)))))
    : String}
  {==}
