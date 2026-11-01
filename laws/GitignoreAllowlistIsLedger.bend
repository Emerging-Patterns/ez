# After `ez add`, `ez remove` or `ez lock --upgrade`, the `.gitignore`
# allowlist names exactly the hashes of dependencies marked `vendor = true`,
# and every other line of `.gitignore` is unchanged.
#
# This guarantee is proved for `ez add`, `ez remove` and `ez lock
# --upgrade`. Over the line-level function `I.lines`
# (src/ledger/ignore.bend), its allowlist lines are exactly the vendored
# hashes, each once, in the order the ledger first names them, and every
# other line is kept in order; the file `I.sync` writes reads back
# (`I.file.lines`) as those lines, whatever the file it read ended with, and
# applying it twice is applying it once; each for a ledger whose vendored
# hashes hold no newline. `ez remove` and `ez add` leave `.gitignore`
# holding exactly `I.sync`'s text over the ledger they leave
# (`remove_syncs_allowlist`, `add_syncs_allowlist`). `ez lock --upgrade`:
# every `.gitignore` its plan writes has the allowlist of the hashes the
# upgrade commits and keeps every other line of the file it read, when no
# source it read is at `.gitignore`; an upgrade that does not refuse and
# leaves `.gitignore` unwritten read one whose allowlist is already those
# hashes (`upgrade_allowlist_kept_in_sync`); and the hashes it commits are
# the vendored hashes of the model it renders when it writes ez.toml
# (`upgrade_vends_the_ledger`) and of ez.toml as it is when it does not
# (`upgrade_unmoved_vends_the_ledger`). `ez add`'s half and the upgrade's
# hold of ez.toml's bytes, since the ledger they leave reads back as the
# model they render (laws/WrittenLedgerReadsBack.bend).
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/ledger/ignore.bend as I
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/remove/plan.bend as RP
import ./defs/LockInputs.bend as D1
import ./defs/WorldAfterLock.bend as D2

# LAW: the gitignore allowlist names exactly the hashes of the dependencies
# the ledger marks `vendor = true`, each once, in the order the ledger first
# names them, whatever the file said before. `ez add`, `ez remove` and `ez
# lock --upgrade` write the file `I.sync` makes from these lines, so after
# any of them the allowlist is the ledger's and no one else's.
law allowlist_is_the_ledger:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  {I.hashes(I.lines(ds, ls)) == I.vended(ds) : List<&2, String>}

# LAW: and every line that is not ez's is kept, in order, as it was written.
# ez's lines are the allowlist, the three rules it needs, and a `.ez/` that
# would make it inert; everything else in the file is the project's.
law allowlist_keeps_other_lines:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  {I.others(I.lines(ds, ls)) == I.others(ls) : List<&2, String>}

# The text layer. `I.sync` reads `.gitignore` into its lines, derives the
# allowlist over them with `I.lines`, and writes them back, each ending with a
# newline; a file whose lines did not change comes back as it was, byte for
# byte. `I.file.lines` is how a file reads as lines: an empty file has none,
# and a last line with no newline after it is a line. Every law below takes a
# ledger whose vendored hashes hold no newline, as a `0x` name never does.

# LAW: after `I.sync`, the allowlist of the file names exactly the vendored
# hashes, each once, in the order the ledger first names them
law sync_allowlist_is_the_ledger:
  for +ds: List<&2, M.Dep>
  for +text: String
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(I.sync(ds, text))) == I.vended(ds) : List<&2, String>}

# LAW: and every line of the file that is not ez's is kept, byte for byte and
# in order
law sync_keeps_other_lines:
  for +ds: List<&2, M.Dep>
  for +text: String
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.others(I.file.lines(I.sync(ds, text))) == I.others(I.file.lines(text))
    : List<&2, String>}

# whether a list of hashes names each hash once. Law vocabulary: ez never
# calls it.
def hashes.distinct(hs: List<&2, String>) -> Bool:
  match hs:
    case []:
      True{}
    case +h <> +t:
      +rest = hashes.distinct(t)
      Bool.and(Bool.not(I.named(t, h)), rest)

# LAW: the allowlist names each vendored hash once. Two dependencies that
# share a tree share its one line, where the first of them is.
law vended_once:
  for ds: List<&2, M.Dep>
  {hashes.distinct(I.vended(ds)) == True{} : Bool}

# LAW: applying `I.sync` twice is applying it once: the file it writes is
# already in sync, and comes back byte for byte
law sync_idempotent:
  for +ds: List<&2, M.Dep>
  for +text: String
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.sync(ds, I.sync(ds, text)) == I.sync(ds, text) : String}

# the hashes whose trees the upgrade commits under `.ez/lib`: the vendored
# hashes of the dependencies it leaves
def vends(world: W.World) -> List<&2, String>:
  Up.next.vends(D1.next.of(world))

# `.gitignore` as the World answered the upgrade
def ignore.read(world: W.World) -> String:
  W.World{_args, _ledger, _listing, _replies, ups} = world
  D2.ignore.said(Up.text.said(ups, Up.Ignore{}))

# LAW: when `ez lock --upgrade` writes `.gitignore`, its allowlist names
# exactly the hashes whose trees the upgrade commits, the vendored hashes of
# the dependencies it leaves, each once. No source the upgrade read is at
# `.gitignore`, and no vendored hash holds a newline.
law upgrade_allowlist_is_the_ledger:
  for +w: W.World
  for +text: String
  for put: {P.put(w, ".gitignore") == P.Put{text} : P.Wrote}
  for +miss: {D2.found.miss(D1.found(w), ".gitignore") == True{} : Bool}
  for +ev: {Str.clear.all(vends(w), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(text)) == vends(w) : List<&2, String>}

# LAW: and keeps every line of the `.gitignore` it read that is not ez's,
# byte for byte and in order
law upgrade_allowlist_keeps_other_lines:
  for +w: W.World
  for +text: String
  for put: {P.put(w, ".gitignore") == P.Put{text} : P.Wrote}
  for +miss: {D2.found.miss(D1.found(w), ".gitignore") == True{} : Bool}
  for +ev: {Str.clear.all(vends(w), '\n') == True{} : Bool}
  {I.others(I.file.lines(text)) == I.others(I.file.lines(ignore.read(w)))
    : List<&2, String>}

# LAW: and when it writes ez.toml, the hashes it commits are the vendored
# hashes of the ledger model it renders there, `P.ledger.next`, so the
# allowlist is that of the ledger ez.toml reads back as
# (laws/WrittenLedgerReadsBack.bend)
law upgrade_vends_the_ledger:
  for +w: W.World
  for +text: String
  for put: {P.put(w, "ez.toml") == P.Put{text} : P.Wrote}
  for +miss: {D2.found.miss(D1.found(w), "ez.toml") == True{} : Bool}
  {vends(w) == I.vended(D1.ledger.deps(P.ledger.next(w))) : List<&2, String>}

# LAW: when `ez lock --upgrade` does not refuse and leaves `.gitignore`
# unwritten, it leaves it because it was in sync already: the file it read
# has the allowlist of exactly the hashes the upgrade commits, each once. No
# vendored hash holds a newline.
law upgrade_allowlist_kept_in_sync:
  for +w: W.World
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for kept: {P.put(w, ".gitignore") == P.Kept{} : P.Wrote}
  for +ev: {Str.clear.all(vends(w), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(ignore.read(w))) == vends(w) : List<&2, String>}

# LAW: and when it leaves ez.toml unwritten, which it does when no pin
# moved, the hashes it commits are the vendored hashes of ez.toml as it is
law upgrade_unmoved_vends_the_ledger:
  for +w: W.World
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for kept: {P.put(w, "ez.toml") == P.Kept{} : P.Wrote}
  {vends(w) == I.vended(D1.ledger.deps(W.parsed(W.ledger.of(w)))) : List<&2, String>}

# LAW: and leaves `.gitignore` holding exactly the file `I.sync` derives from
# the dependencies of that ledger: written when that changes it, kept as it
# was when it does not. `allowlist_is_the_ledger` and
# `allowlist_keeps_other_lines` say what that file's lines are.
law add_syncs_allowlist:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.after(P.put.plan(AP.plan(w), ".gitignore"), A.ignore(w))
    == I.sync(A.deps.of(Rend.add.keep(m, AP.added(w))), A.ignore(w)) : String}

# LAW: and leaves `.gitignore` holding exactly the file `I.sync` derives from
# the dependencies that are left: written when that changes it, kept as it
# was when it does not. `allowlist_is_the_ledger` and
# `allowlist_keeps_other_lines` say what that file's lines are.
law remove_syncs_allowlist:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for +good: {M.Good{m} == M.parse(s) : M.Read}
  for ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  {RP.after(P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), ".gitignore"), ignore)
    == I.sync(RP.deps.of(Rend.remove(m, name)), ignore) : String}
