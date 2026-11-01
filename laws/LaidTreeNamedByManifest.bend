# When ez writes a package under `<lib>/<h>`, `h` is the 0x hash of the file
# list whose manifest it writes beside the files.
#
# This guarantee is proved of every command that lays a tree. Over the
# package walk (`src/pkg/pkg.bend`), the `0x` name of the files it found,
# and their manifest, are the name and the manifest of the files it lays,
# each weighed by its own text. `ez add`, `ez fetch` and `ez lock`, plain or
# `--upgrade`: every tree the plan lays has the manifest of the texts it
# lays as its last file, each weighed by its own text, and is named by that
# manifest's `0x` hash (`add_lays_named`, `add_named_lays_named`,
# `fetch_lays_named`, `lock_lays_named`, all over `P.lays.named`). `ez add
# <name>@<version>` judges the package the hub serves as `ez lock` judges a
# hub package, so one whose manifest does not hash to the name the hub
# answered is refused, never laid (`add_named_refuses_manifest`). The lock
# checks, besides the manifest's digest and each file's sum, that the files
# it lays hash to the name, and lays the manifest of those files, so a
# package whose manifest hashes to its name but is not written the way the
# name is taken is refused, not locked (see docs/rfc/ez-spec.md, "Decided
# behavior changes").
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# LAW: a walked package is named by the manifest of the very texts it lays.
# The hash is the `0x` name of the files the walk found, each weighed by its
# own text, so a plan that lays those files under that hash, with that
# manifest beside them, writes a directory whose name is the digest of its
# manifest. This is laws/LaidTreeNamedByManifest.bend for the walk.
law walked_named_by_texts:
  for +pre: String
  for +out: List<&2, K.Hit>
  {K.hash_of(K.placed(pre, K.hit.sums(out)))
    == K.hash_of(K.laid.sums(K.laid(pre, out))) : String}

# LAW: and so the manifest written beside them is the manifest of those texts
law walked_manifest_of_texts:
  for +pre: String
  for +out: List<&2, K.Hit>
  {K.manifest_of(K.placed(pre, K.hit.sums(out)))
    == K.manifest_of(K.laid.sums(K.laid(pre, out))) : String}

# LAW: every tree `ez lock` lays, plain or `--upgrade`, has the manifest of
# the texts it lays as its last file, each weighed by its own text, and is
# named by that manifest's `0x` hash. A package whose manifest hashes to its
# name but is not written the way the name is taken is refused, not laid.
law lock_lays_named:
  for +w: W.World
  {P.lays.named(P.effects(P.plan(w))) == True{} : Bool}

# LAW: every tree `ez add` lays is named by the manifest of the texts it
# lays: its last file is the manifest of the others, each weighed by its own
# text, and its hash is that manifest's `0x` name
law add_lays_named:
  for +w: A.World
  {P.lays.named(P.effects(AP.plan(w))) == True{} : Bool}

# LAW: every tree the add lays is named by the manifest of the texts it
# lays, and its hash is that manifest's `0x` name
law add_named_lays_named:
  for +w: A.World
  {P.lays.named(P.effects(H.plan(w))) == True{} : Bool}

# LAW: every tree `ez fetch` lays has the manifest of the texts it lays as its
# last file, each weighed by its own text, and is named by that manifest's
# `0x` hash, so a lock that records files under a name they do not hash to
# lays nothing
law fetch_lays_named:
  for +w: F.World
  {P.lays.named(FP.effects(FP.plan(w))) == True{} : Bool}
