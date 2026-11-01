import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/up.bend as Up

# LAW: and `ez lock --upgrade` weighs a pinned commit the same way: when the
# walk's hash is not the pin, the pin is compared with the checkout's hash
# without its LICENSE files, which is the pin exactly when it was taken so
law upgrade_named_without_license:
  for +pin: String
  for +manifest: String
  for walked: {False{} == String.eq(Up.hash.of(manifest), pin) : Bool}
  for bare: {True{} == String.eq(Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(
    String.lines(manifest))))), pin) : Bool}
  {Up.hash.kept(pin, manifest)
    == Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))))
    : String}
