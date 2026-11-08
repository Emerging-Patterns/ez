import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/up.bend as Up

# LAW: and `ez lock --upgrade` weighs a pinned commit the same way: when
# neither the walk's hash nor the checkout's without its README is the pin
# (laws/UpgradeNamedWithoutReadme.bend), the pin is compared with the
# checkout's hash without its README and its LICENSE files, which is the pin
# exactly when it was taken so
law upgrade_named_without_license:
  for +pin: String
  for +manifest: String
  for walked: {False{} == String.eq(Up.hash.of(manifest), pin) : Bool}
  for readmeful: {False{} == String.eq(Up.hash.of(K.manifest.lines(K.readmeless(
    L.manifest.files(String.lines(manifest))))), pin) : Bool}
  for bare: {True{} == String.eq(Up.hash.of(K.manifest.lines(K.bare(K.readmeless(
    L.manifest.files(String.lines(manifest)))))), pin) : Bool}
  {Up.hash.kept(pin, manifest)
    == Up.hash.of(K.manifest.lines(K.bare(K.readmeless(L.manifest.files(String.lines(manifest))))))
    : String}
