# `ez publish` uploads only when every hub package the package imports is on
# the hub the ledger names: for each `0x<hash>/...` import in the package's
# files the hub serves a manifest that hashes to that name, and for each
# `<name>@<version>/...` import the hub resolves the name to a `0x` name, the
# one the lock or the ledger resolved it to when either records one. Before
# the upload it asks the hub about each; a package the hub does not have, and
# a hub that could not be asked, refuse with exit 1, naming each such import
# and the dependency key and origin the ledger records for it, and nothing is
# sent.
#
# This guarantee is proved over the plan `ez publish` runs
# (`src/pub/plan.bend`). Past the check that git tracks every file, the
# planner collects the hub imports of the files the walk made, each `0x`
# name and each `<name>@<version>` once, reads the lock when there is a name
# among them, and asks the ledger's hub about each (`PP.hubbed`). A World
# gets as far as the upload only when every one is on the hub
# (`pub_sends_only_on_hub`), so one that is off it sends nothing
# (`pub_offhub_sends_nothing`) and refuses (`pub_offhub_refuses`), and one
# import off the hub is enough wherever it stands among them
# (`hub_one_off_is_off`). What counts as off is stated over the answer: a
# 404 is a package the hub does not have (`hub_404_is_absent`), any other
# answer that is not a 200, the hub unreachable among them, is a hub that
# could not be asked, which refuses too (`hub_unreachable_is_off`), and a
# name the hub resolves to a hash other than the one the lock records is not
# the package imported (`hub_name_elsewhere_is_off`), while one it resolves
# to that hash is (`hub_name_there`). A manifest the hub serves for a `0x`
# name counts only when it hashes to that name, as `ez lock` checks it. What
# the laws take from the interpreter is trusted in src/ez/app.bend: that it
# GETs the url each question names under the ledger's hub, as `ez lock`
# does, and reads the lock from ez.lock.toml.
import Base
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/lock/lock.bend as L
import ../src/add/world.bend as A

# ---------------------------------------------------------------------------
# the hub packages the package imports

# LAW: `ez publish` gets as far as the upload only on a World in which every
# hub package the package imports, by its `0x` name or by its
# `<name>@<version>`, is on the hub (`PP.on.hub`): the hub served its
# manifest, or resolved its name to the hash the lock records. A package
# that imports one the hub lacks could not be built from the hub.
law pub_sends_only_on_hub:
  for +w: PW.World
  for s: {PP.sends(w) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

# LAW: so a World in which one of them is off the hub, or the hub could not
# be asked, never gets as far as the upload
law pub_offhub_sends_nothing:
  for +w: PW.World
  for +why: String
  for e: {PP.hubbed(w) == PP.OffHub{why} : PP.Hubbed}
  {PP.sends(w) == False{} : Bool}

# LAW: and refuses, exiting 1
law pub_offhub_refuses:
  for +w: PW.World
  for +why: String
  for e: {PP.hubbed(w) == PP.OffHub{why} : PP.Hubbed}
  {PP.succeeds(w) == False{} : Bool}

# LAW: one hub import off the hub is enough, wherever it stands among them:
# the rest being on the hub does not make up for it
law hub_one_off_is_off:
  for +w: PW.World
  for +hub: String
  for +ds: List<&2, M.Dep>
  for pre: List<&2, PP.Probe>
  for +p: PP.Probe
  for +post: List<&2, PP.Probe>
  for +line: String
  for e: {PP.seen(w, hub, ds, p) == PP.Off{line} : PP.Seen}
  {PP.on.hub.v(PP.hubbed.of(PP.tally(w, hub, ds, List.append(&2, PP.Probe, pre, p <> post)), hub))
    == False{} : Bool}

# LAW: a hub that answers 404 does not have the package, and the refusal
# says to publish it first
law hub_404_is_absent:
  for p: PP.Probe
  for +who: String
  {PP.seen.ran(p, False{}, "the server answered 404", who) == PP.Off{PP.why.absent(who)}
    : PP.Seen}

# LAW: and any other answer that is not a 200, the hub unreachable among
# them, is a hub that could not be asked, which refuses too: nothing is sent
# on a guess
law hub_unreachable_is_off:
  for p: PP.Probe
  for +text: String
  for +who: String
  for e: {PP.absent(text) == False{} : Bool}
  {PP.seen.ran(p, False{}, text, who) == PP.Off{PP.why.unasked(who, text)} : PP.Seen}

# LAW: a name the hub resolves to a hash other than the one the lock records
# is not the package imported
law hub_name_elsewhere_is_off:
  for +got: String
  for +want: String
  for +who: String
  for e0: {String.eq(got, want) == False{} : Bool}
  for e1: {String.is_empty(want) == False{} : Bool}
  {PP.seen.named(got, want, who) == PP.Off{PP.why.named(got, want, who)} : PP.Seen}

# LAW: and one it resolves to that hash, a `0x` name, is on the hub
law hub_name_there:
  for +got: String
  for +want: String
  for +who: String
  for e0: {String.eq(got, want) == True{} : Bool}
  for e1: {L.hash.ok(got) == True{} : Bool}
  {PP.seen.named(got, want, who) == PP.There{} : PP.Seen}
