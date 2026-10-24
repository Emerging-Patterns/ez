# ws/moved: a workspace member imported by its hash, once its hash moved
# (EZ-WS-7). A member that publishes under no name is imported by its `0x`
# hash, and editing it moves that hash, so an import line written before the
# edit names the hash the lock being rewritten records for it. A plain lock
# writes no source (EZ-DOC-5), so it refuses, before it asks anything, and
# names the upgrade that rewrites the line. That upgrade rewrites every line
# naming a moved member's recorded hash, the way an upgrade rewrites a moved
# dependency's (EZ-VEN-2, EZ-VEN-3), and since a member whose files it
# rewrote has a new hash in turn, it goes round again until no member it
# moves moves any further. Everything here is pure: ws/up.bend plans with it.
import Base
import ../ledger/manifest.bend as M
import ../ledger/upgrade.bend as U
import ../lock/lock.bend as L
import ../lock/world.bend as LW
import ../lock/plan.bend as LP
import ../pkg/pkg.bend as K
import ../toml/toml.bend as T
import ./joint.bend as J

# a member's package: the directory it is written from, the name the joint
# ledger gives it ("" where the lock is read, which records none), and its
# hash
type Held is Data:
  Held{path: String, name: String, hash: String}

# a member whose hash moves: its name, the hash the lock records, and the
# hash it has now
type Shift is Data:
  Shift{name: String, old: String, new: String}

# ---------------------------------------------------------------------------
# what the lock records, and what the members are now

# a package of the lock being rewritten, when it is a member's
def locked.src(src: L.Src, +hash: String) -> List<&2, Held>:
  match src:
    case L.Hub{}:
      []
    case L.Git{_url, _rev, _entry, _root, _nar, _tag}:
      []
    case L.Member{path, _entry}:
      [Held{path, "", hash}]

# every member package of a lock's packages
def locked.all(ps: List<&2, L.Pack>) -> List<&2, Held>:
  match ps:
    case []:
      []
    case L.Pack{+hash, src, _files} <> tl:
      List.append(&2, Held, locked.src(src, hash), locked.all(tl))

# every member package the lock being rewritten records, from its text
def locked(+text: String) -> List<&2, Held>:
  locked.all(L.packs(T.sects(T.parse(text))))

# a dependency of the joint ledger, when it is a member's
def now.src(src: M.Source, +name: String, +hash: String) -> List<&2, Held>:
  match src:
    case M.Hub{_nv}:
      []
    case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
      []
    case M.Member{path, _nv}:
      [Held{path, name, hash}]

# every member the joint ledger depends on
def now.all(ds: List<&2, M.Dep>) -> List<&2, Held>:
  match ds:
    case []:
      []
    case M.Dep{+nn, +hh, _ee, src} <> tl:
      List.append(&2, Held, now.src(src, nn, hh), now.all(tl))

# every member the joint ledger depends on, or none when there is none
def now(jj: J.Joint) -> List<&2, Held>:
  match jj:
    case J.Lone{}:
      []
    case J.Clash{_why}:
      []
    case J.Joint{mm}:
      now.all(J.deps.of(mm))

# the directory a member is written from
def held.path(hd: Held) -> String:
  Held{hp, _hn, _hh} = hd
  hp

# the member written from a directory, once it is known whether the head is
def at.pick(hit: Bool, hd: Held, rest: Maybe<&2, Held>) -> Maybe<&2, Held>:
  match hit:
    case True{}:
      Some{hd}
    case False{}:
      rest

# the first member written from a directory, or none
def at(hs: List<&2, Held>, +path: String) -> Maybe<&2, Held>:
  match hs:
    case []:
      None{}
    case +hd <> tl:
      rest = at(tl, path)
      at.pick(String.eq(held.path(hd), path), hd, rest)

# a member's hash, or "" for none
def hash.of(found: Maybe<&2, Held>) -> String:
  match found:
    case None{}:
      ""
    case Some{hd}:
      Held{_hp, _hn, hh} = hd
      hh

# ---------------------------------------------------------------------------
# which members move

# a move kept, once it is known whether it is one
def move.put(hit: Bool, +name: String, +old: String, +new: String, rest: List<&2, Shift>) -> List<&2, Shift>:
  match hit:
    case True{}:
      Shift{name, old, new} <> rest
    case False{}:
      rest

# the member the lock records at a directory, against what it is now: it
# moves when its hash is not the one the lock records, and it is chosen
# (`--package`, or every member when none is given) or its hash is not the
# one it had before any line was rewritten, which is a member whose files
# the upgrade rewrote
def move.found(
  found: Maybe<&2, Held>,
  +base: String,
  +old: String,
  +only: String,
  rest: List<&2, Shift>
) -> List<&2, Shift>:
  match found:
    case None{}:
      rest
    case Some{hd}:
      Held{_hp, +name, +new} = hd
      move.put(Bool.and(Bool.not(String.eq(new, old)),
        Bool.or(U.chosen(only, name), Bool.not(String.eq(new, base)))), name, old, new, rest)

# every member the lock records that moves: `now` the members as they are,
# `base` as they were before any line was rewritten
def moves(
  old: List<&2, Held>,
  +now: List<&2, Held>,
  +base: List<&2, Held>,
  +only: String
) -> List<&2, Shift>:
  match old:
    case []:
      []
    case Held{+path, _name, +hash} <> tl:
      rest = moves(tl, now, base, only)
      move.found(at(now, path), hash.of(at(base, path)), hash, only, rest)

# the moves as the rewrites they make
def swaps(ms: List<&2, Shift>) -> List<&2, U.Swap>:
  match ms:
    case []:
      []
    case Shift{_name, old, new} <> tl:
      U.Swap{old, new} <> swaps(tl)

# every committed file with every moved hash rewritten
def rewrite(+ss: List<&2, U.Swap>, fs: List<&2, K.Source>) -> List<&2, K.Source>:
  match fs:
    case []:
      []
    case K.Source{at, text} <> tl:
      K.Source{at, U.reimport.many(ss, text)} <> rewrite(ss, tl)

# ---------------------------------------------------------------------------
# a plain lock: a line naming a moved member's recorded hash

# why a file stops a plain lock: the first move one of its lines names
def stale.moves(ms: List<&2, Shift>, +at: String, +text: String) -> String:
  match ms:
    case []:
      ""
    case Shift{+name, +old, +new} <> tl:
      rest = stale.moves(tl, at, text)
      Bool.pick(String, String.eq(U.reimport.many([U.Swap{old, new}], text), text), rest,
        "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
          ", the hash the lock records for it, and the member is " ++ new ++
          " now; ez lock --upgrade --package " ++ name ++ " rewrites the import")

# why a plain lock refuses: the first committed file with a line naming a
# moved member's recorded hash, "" when none does
def stale(+ms: List<&2, Shift>, fs: List<&2, K.Source>) -> String:
  match fs:
    case []:
      ""
    case K.Source{+at, +text} <> tl:
      +here = stale.moves(ms, at, text)
      rest = stale(ms, tl)
      Bool.pick(String, String.is_empty(here), rest, here)

# the members of a ledger's text, as the joint ledger renders them
def now.read(rd: M.Read) -> List<&2, Held>:
  match rd:
    case M.Bad{_why}:
      []
    case M.Good{mm}:
      now.all(J.deps.of(mm))

# and of the World's ledger
def now.ledger(ledger: Maybe<&2, String>) -> List<&2, Held>:
  match ledger:
    case None{}:
      []
    case Some{text}:
      now.read(M.parse(text))

# every member that moved since the lock being rewritten, against the
# joint ledger the lock is planned from
def moved(+lock: String, ledger: Maybe<&2, String>) -> List<&2, Shift>:
  +now = now.ledger(ledger)
  moves(locked(lock), now, now, "")

# why a plain lock at a workspace root refuses before it asks anything, ""
# when it does not
def stale.world(+lock: String, world: LW.World) -> String:
  LW.World{_args, ledger, listing, _replies, _ups} = world
  stale(moved(lock, ledger), J.files(listing))

# ---------------------------------------------------------------------------
# the upgrade: rewrite, walk again, until nothing moves further

# whether two moves are one
def move.eq(aa: Shift, bb: Shift) -> Bool:
  Shift{an, ao, aw} = aa
  Shift{bn, bo, bw} = bb
  Bool.and(String.eq(an, bn), Bool.and(String.eq(ao, bo), String.eq(aw, bw)))

# whether two lists of moves are one
def moves.eq(aa: List<&2, Shift>, bb: List<&2, Shift>) -> Bool:
  match aa bb:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{_b, _bt}:
      False{}
    case Con{_a, _at} Nil{}:
      False{}
    case Con{a, at} Con{b, bt}:
      rest = moves.eq(at, bt)
      Bool.and(move.eq(a, b), rest)

# what a round of the upgrade sees: the root's ledger text, every other
# ez.toml git lists, the committed files as they are, the members the lock
# records, the members before any line was rewritten, and `--package`
type Ctx is Data:
  Ctx{text: String, found: List<&2, J.Found>, files: List<&2, K.Source>, old: List<&2, Held>,
    base: List<&2, Held>, only: String}

# the moves the next round makes: the files rewritten with this round's
# moves, the members walked again over them, and the moves against those
def round(ctx: Ctx, ms: List<&2, Shift>) -> List<&2, Shift>:
  Ctx{+text, +fs, +files, old, base, +only} = ctx
  moves(old, now(J.joint(text, fs, rewrite(swaps(ms), files))), base, only)

# the moves once a round is known to change them or not; the rounds after it
# arrive as a thunk, so the rounds stop where the moves do
def cascade.pick(same: Bool, ms: List<&2, Shift>, rest: Unit -> List<&2, Shift>) -> List<&2, Shift>:
  match same:
    case True{}:
      ms
    case False{}:
      rest(Unit{})

# rounds, under fuel, until one moves no member further
def cascade.go(fuel: Nat, +ctx: Ctx, +ms: List<&2, Shift>) -> List<&2, Shift>:
  match fuel:
    case 0n:
      ms
    case 1n+f:
      +next = round(ctx, ms)
      cascade.pick(moves.eq(ms, next), ms, _u => cascade.go(f, ctx, next))

# the context of an upgrade's rounds
def ctx(+text: String, +fs: List<&2, J.Found>, +files: List<&2, K.Source>, +lock: String, +only: String) -> Ctx:
  Ctx{text, fs, files, locked(lock), now(J.joint(text, fs, files)), only}

# the members the upgrade moves, from the ones it is asked to. Each round
# moves at least one more member or ends, and a member moves once, so a
# round per member the lock records and one more is fuel enough.
def cascade(+cx: Ctx) -> List<&2, Shift>:
  Ctx{text, fs, files, +old, +base, only} = cx
  cascade.go((List.length(&2, Held, old) + 1n : Nat), Ctx{text, fs, files, old, base, only},
    moves(old, base, base, only))

# a rewritten file written, when the rewrite changed it and it is not the lock
def edit.put(changed: Bool, +at: String, text: String, +rest: List<&2, LP.Effect>) -> List<&2, LP.Effect>:
  match changed:
    case True{}:
      Bool.pick(List<&2, LP.Effect>, String.eq(at, LP.lockfile()), rest, LP.Write{at, text} <> rest)
    case False{}:
      rest

# every file the moves rewrite, written
def edits(+ss: List<&2, U.Swap>, fs: List<&2, K.Source>) -> List<&2, LP.Effect>:
  match fs:
    case []:
      []
    case K.Source{+at, +text} <> tl:
      +new = U.reimport.many(ss, text)
      edit.put(Bool.not(String.eq(new, text)), at, new, edits(ss, tl))

# the committed files as the lock is to read them
def sources(fs: List<&2, K.Source>) -> List<&2, LW.Source>:
  match fs:
    case []:
      []
    case K.Source{at, text} <> tl:
      LW.Source{at, text} <> sources(tl)

# the World the upgrade plans on: the committed files rewritten with every
# move, and the joint ledger and the answers for its members made again over
# them, so the lock walks the members as the rewrite leaves them
def world.moved(
  +jj: J.Joint,
  +files: List<&2, K.Source>,
  world: LW.World
) -> LW.World:
  LW.World{args, +ledger, _listing, replies, ups} = world
  LW.World{args, J.joint.text(jj, ledger), LW.Listed{sources(files)},
    List.append(&2, LW.Reply, replies, J.seeds(jj, files)), ups}
