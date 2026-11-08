import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/hub/hub.bend as Web

# A ledger written before bend 2.0.40 names a git package without the README
# 2.0.40 takes along, and the walk of the same checkout now carries it. The
# name decides which package it is, as it does for a name taken before 2.0.27
# without the LICENSE files (laws/GitNamedWithoutLicense.bend): `ez lock` and
# `ez lock --upgrade` take the checkout as it was named, and `ez add` names a
# new pin with its README.

# LAW: a git package whose walked manifest is not the one its name is the
# digest of, and whose manifest without its README is, is judged without its
# README, so a ledger written before bend 2.0.40 locks the same checkout as
# it did
law git_named_without_readme:
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for unnamed: {False{} == Web.matches(L.want(hash), manifest) : Bool}
  for readmeless: {True{} == Web.matches(L.want(hash),
    K.manifest.lines(K.readmeless(L.manifest.files(String.lines(manifest))))) : Bool}
  {W.git.weighed("", hash, manifest, ss)
    == W.git.body(List.is_empty(&2, K.Item, K.readmeless(L.manifest.files(String.lines(manifest)))),
      hash, K.manifest.lines(K.readmeless(L.manifest.files(String.lines(manifest)))),
      K.readmeless.srcs(L.manifest.files(String.lines(manifest)), ss)) : W.Verdict}
