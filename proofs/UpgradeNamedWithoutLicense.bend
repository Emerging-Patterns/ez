# proofs of laws/UpgradeNamedWithoutLicense.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/up.bend as Up
import ../laws/UpgradeNamedWithoutLicense.bend as Laws

def Laws.upgrade_named_without_license(pin, manifest, walked, bare):
  %walked : {Up.hash.kept.pick(_, pin, Up.hash.of(manifest), manifest)
    == Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))))
    : String}
  %bare : {Up.hash.kept.or(_,
      Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest))))),
      Up.hash.of(manifest))
    == Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))))
    : String}
  {==}
