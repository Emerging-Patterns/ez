# ws/pin: the ref `ez add` in a workspace member takes (EZ-WS-4). A git source
# has one pin across a workspace, so a member adding a source another member
# already records takes that pin: with no ref, the tag it records, or its
# commit when it records none; with the tag or commit it records, that; with
# any other ref, nothing, since moving the source is an upgrade of every
# member that records it. A source no member records, and a hub package, take
# the ref as it was given.
import Base
import ../ledger/manifest.bend as M
import ../pkg/path.bend as P
import ../ez/target.bend as Tgt
import ../add/world.bend as A
import ./joint.bend as J

# the ref an add goes on with, or why it stops
type Ref is Data:
  Given{ref: String}
  Held{why: String}

# the ref the workspace pins a source at: its tag, or its commit when it has
# no tag
def held(+rev: String, +tag: String) -> String:
  Bool.pick(String, String.is_empty(tag), rev, tag)

# a ref given against the pin the workspace records for the source
def ref.pinned(+url: String, +rev: String, +tag: String, +ref: String) -> Ref:
  Bool.pick(Ref, String.is_empty(ref), Given{held(rev, tag)},
    Bool.pick(Ref, Bool.or(String.eq(ref, tag), String.eq(ref, rev)), Given{ref},
      Held{"ez: the workspace pins " ++ url ++ " at " ++ held(rev, tag) ++
        "; move it for every member with ez lock --upgrade --package"}))

# a ref given against what the workspace records for the source, if anything
def ref.at(src: M.Source, +url: String, +ref: String) -> Ref:
  match src:
    case M.Hub{_nv}:
      Given{ref}
    case M.Git{_u, +rev, +tag, _o, _n, _v}:
      ref.pinned(url, rev, tag, ref)

# a place's ref: a git source's against the workspace's pins, as the root
# reads the source from the member's directory, and anything else as given
def ref.place(place: Tgt.Place, +pins: List<&2, M.Dep>, +dir: String, +home: String, +ref: String) -> Ref:
  match place:
    case Tgt.Bad{_why}:
      Given{ref}
    case _:
      +url = P.anchor(dir, A.url.of(place, home))
      ref.at(J.pin.of(pins, url), url, ref)

# the ref `ez add <target> [ref]` in a member goes on with: `pins` is every
# dependency of the workspace's joint ledger and `dir` the member's directory
# from the root. A hub package, added by its `<name>@<version>`, has no ref.
def ref(+pins: List<&2, M.Dep>, +dir: String, +home: String, +target: String, +ref: String) -> Ref:
  Bool.pick(Ref, Tgt.aim.named(Tgt.aim(target)), Given{ref},
    ref.place(Tgt.classify(target), pins, dir, home, ref))
