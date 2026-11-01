import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/hub/hub.bend as Web
import ../src/add/world.bend as A

# A ledger written before bend 2.0.27 names a git package without the LICENSE
# files 2.0.27 takes along, and the walk of the same checkout now carries them.
# The name decides which package it is: `ez lock` and `ez lock --upgrade` take
# the checkout as it was named, and `ez add` names a new pin with them.

# LAW: a git package whose walked manifest is not the one its name is the
# digest of is judged without its LICENSE files, so a ledger written before
# bend 2.0.27 locks the same checkout as it did
law git_named_without_license:
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for unnamed: {False{} == Web.matches(L.want(hash), manifest) : Bool}
  {W.git.weighed("", hash, manifest, ss)
    == W.git.body(List.is_empty(&2, K.Item, K.bare(L.manifest.files(String.lines(manifest)))),
      hash, K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))),
      K.bare.srcs(L.manifest.files(String.lines(manifest)), ss)) : W.Verdict}
