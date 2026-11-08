# the World a lock leaves for the next run to read, and what it keeps of the
# ledger, .gitignore and sources
import Base
import ../../src/pkg/pkg.bend as K
import ../../src/toml/toml.bend as T
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/upgrade.bend as U
import ../../src/lock/plan.bend as P
import ../../src/lock/lock.bend as L
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ./LockInputs.bend as D1

# Import rewriting (laws/UpgradeRewritesImports.bend,
# laws/RewriteKeepsOtherLines.bend). When an upgrade moves hashes it
# rewrites every source with `U.reimport.many`, which cuts the text at its
# newlines, rewrites each line through every move in order, and joins the
# lines back. A line names a hash when it starts `import <hash>/`, at column
# 0. The moves are the upgrade's: each old hash names something, no hash
# holds `/` or a newline, as a `0x` name never does, and no move's new hash
# is the old hash of a move after it, which would move a rewritten line
# again.

# the line at a place in a list of lines, "" past its end. Law vocabulary: ez
# never calls it.
def line.at(ls: List<&2, String>, at: Nat) -> String:
  match ls at:
    case Nil{} _:
      ""
    case h <> t 0n:
      h
    case h <> t 1n+p:
      line.at(t, p)

# whether no move of a list has a hash as its old one
def olds.miss(ss: List<&2, U.Swap>, +hash: String) -> Bool:
  match ss:
    case []:
      True{}
    case U.Swap{o, _n} <> t:
      +rest = olds.miss(t, hash)
      Bool.and(Bool.not(String.eq(o, hash)), rest)

# whether a list of moves is one an upgrade makes: every old hash names
# something, every hash is plain, and no new hash is the old hash of a move
# after it
def moves.ok(ss: List<&2, U.Swap>) -> Bool:
  match ss:
    case []:
      True{}
    case U.Swap{+o, +n} <> +t:
      +rest = moves.ok(t)
      Bool.and(Bool.and(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
        Bool.and(D1.plain(n), olds.miss(t, n))), rest)

# a cloned tree as the next lock reads it: from BEND_LIB when it was laid,
# cloned again when it was not
def after.clone(laid: Bool, +got: String, +manifest: String, +ss: List<&2, String>) -> W.Answer:
  match laid:
    case True{}:
      W.Got{W.Lib{}, manifest, ss}
    case False{}:
      W.Got{W.Clone{got}, manifest, ss}

# one answer by how it arrived. Only a clone that passed is laid.
def after.how(
  how: W.How,
  +orgs: List<&2, L.Origin>,
  +hub: String,
  +hash: String,
  +manifest: String,
  +ss: List<&2, String>
) -> W.Answer:
  match how:
    case W.Lib{}:
      W.Got{W.Lib{}, manifest, ss}
    case W.Clone{+got}:
      after.clone(D1.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
        got, manifest, ss)
    case W.Served{}:
      W.Got{W.Served{}, manifest, ss}

# one answer as the next lock reads it
def after.one(+orgs: List<&2, L.Origin>, +hub: String, +hash: String, answer: W.Answer) -> W.Answer:
  match answer:
    case W.Miss{why}:
      W.Miss{why}
    case W.Got{how, manifest, ss}:
      after.how(how, orgs, hub, hash, manifest, ss)
    case W.Said{text}:
      W.Said{text}
    case W.Locked{text}:
      W.Locked{text}

# every answer, so
def after.all(+orgs: List<&2, L.Origin>, +hub: String, rs: List<&2, W.Reply>) -> List<&2, W.Reply>:
  match rs:
    case []:
      []
    case W.Reply{+ask, answer} <> t:
      W.Reply{ask, after.one(orgs, hub, W.ask.hash(ask), answer)} <> after.all(orgs, hub, t)

# the World after a lock that succeeded: the same flags, ledger and listing,
# and every tree it laid read from BEND_LIB. The trees are judged against the
# ledger the lock was made from, which for a plain lock is ez.toml. What an
# upgrade leaves besides, the ledger and sources it wrote, is WP5b's.
def after.laid(world: W.World) -> W.World:
  W.World{+args, +ledger, listing, replies, +ups} = world
  W.World{args, ledger, listing,
    after.all(W.next.origins(W.next(args, ledger, ups)),
      W.next.hub(W.next(args, ledger, ups)), replies), ups}

# a refused lock writes and lays nothing, so it leaves the World it read
def after.pick(refused: Bool, world: W.World) -> W.World:
  match refused:
    case True{}:
      world
    case False{}:
      after.laid(world)

# What `ez lock --upgrade` leaves besides. An upgrade that succeeds writes
# ez.toml when a pin moved, `.gitignore` when its allowlist changed, and every
# source whose imports name a moved hash, and lays each tree it moved to, under
# `.ez/lib` when the ledger it leaves vendors it and under BEND_LIB otherwise.
# The next lock reads that ledger, the committed sources as the upgrade
# rewrote them (`W.listing.of`, the sources the lock itself was made from),
# and each tree it laid from BEND_LIB with the bytes laid. A vendored tree is
# read from there when BEND_LIB is `.ez/lib`, which is its default; with
# BEND_LIB elsewhere it is cloned again, which `clone_reproduces` says locks
# the same. That the files `find` rewrote are the files the listing holds is
# the interpreter's side (trusted in src/ez/app.bend).
#
# The remote is taken not to change between the two runs: every question the
# second upgrade asks a remote (refs, the default branch, tags, ancestry, a
# checkout at a rev, a weighing, the hub's word on a hash) is answered as the
# first run's answers say, so its answers are the first run's list. Only the
# local file it reads, `.gitignore`, has a new answer, which comes first, so
# it is the one the next upgrade reads. It asks for the sources only when a
# hash moves.

# the text the upgrade's edits leave at ez.toml: the first edit there, or the
# ledger as it was when there is none. An upgrade edits ez.toml once at most.
def ledger.pick(hit: Bool, text: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{text}
    case False{}:
      rest

def ledger.left(es: List<&2, Up.Edit>, ledger: Maybe<&2, String>) -> Maybe<&2, String>:
  match es:
    case []:
      ledger
    case Up.Edit{at, text} <> t:
      ledger.pick(String.eq(at, "ez.toml"), text, ledger.left(t, ledger))

# and at `.gitignore`: the first edit there, or the text the upgrade read
def ig.pick(hit: Bool, text: String, rest: String) -> String:
  match hit:
    case True{}:
      text
    case False{}:
      rest

def ig.left(es: List<&2, Up.Edit>, now: String) -> String:
  match es:
    case []:
      now
    case Up.Edit{at, text} <> t:
      ig.pick(String.eq(at, ".gitignore"), text, ig.left(t, now))

# the `.gitignore` an upgrade read, "" when it read none (`ignore.said`
# below, which reads a World)
def ig.said(said: Up.Said) -> String:
  match said:
    case Up.Said{text}:
      text
    case Up.Unsaid{_why}:
      ""
    case Up.Unasked{_ask}:
      ""

def ig.read(+ups: List<&2, Up.Reply>) -> String:
  ig.said(Up.text.said(ups, Up.Ignore{}))

# the World after an upgrade that succeeded: the same flags; the ledger it
# wrote; the committed sources as it rewrote them; every tree the lock read,
# including the ones the upgrade checked out, read from BEND_LIB when it was
# laid; and the same remote answers, behind `.gitignore` as it left it
def after.up.laid(world: W.World) -> W.World:
  W.World{+args, +ledger, listing, replies, +ups} = world
  +nx = W.next(args, ledger, ups)
  W.World{args, ledger.left(Up.next.edits(nx), ledger), W.listing.of(nx, listing),
    after.all(W.next.origins(nx), W.next.hub(nx), W.replies.of(nx, replies)),
    Up.Reply{Up.Ignore{}, Up.Plain{ig.left(Up.next.edits(nx), ig.read(ups))}} <> ups}

# a refused upgrade writes and lays nothing, so it leaves the World it read
def after.up.pick(refused: Bool, world: W.World) -> W.World:
  match refused:
    case True{}:
      world
    case False{}:
      after.up.laid(world)

def after.mode(up: Bool, +world: W.World) -> W.World:
  match up:
    case False{}:
      after.pick(P.refuses(world), world)
    case True{}:
      after.up.pick(P.refuses(world), world)

# the World `ez lock` leaves, plain or `--upgrade`, for the next lock to read.
# Law vocabulary: ez never calls it.
def after(+world: W.World) -> W.World:
  after.mode(W.args.upgrade(world), world)

# the hashes it moved, each with the hash that replaces it in an import
def swaps(world: W.World) -> List<&2, U.Swap>:
  Up.next.swaps(D1.next.of(world))

# a file's text as the World answered it, "" when it did not
def ignore.said(said: Up.Said) -> String:
  match said:
    case Up.Said{text}:
      text
    case Up.Unsaid{_why}:
      ""
    case Up.Unasked{_ask}:
      ""

# whether no source of a list is at a path
def found.miss(fs: List<&2, Up.Found>, +path: String) -> Bool:
  match fs:
    case []:
      True{}
    case Up.Found{at, _text} <> t:
      +rest = found.miss(t, path)
      Bool.and(Bool.not(String.eq(at, path)), rest)

# what a path holds after a plan: what the plan wrote there, or what it held
def left.at(wrote: P.Wrote, +before: String) -> String:
  match wrote:
    case P.Kept{}:
      before
    case P.Put{text}:
      text

# That the lock's text reads back as its tables is trusted in
# src/lock/lock.bend, through eztoml's round trip (trusted in
# src/toml/toml.bend): ez writes it as eztoml's `render` of the document it
# assembles. What is left here is ez's side: what ez reads out of the
# tables, `L.packs`, `L.lock.hub` and `M.tools`, and what it gives back: the
# packages in hash order with their files in path order and each once, which
# is `canon`, and each tool without `vendor`, which the lock does not write,
# which is `tools.canon`. Law vocabulary: ez never calls these.

# the tables a lock renders after its packages: the `[names]` table, when it
# resolved a name, then every tool's table. Law vocabulary.
def tail(nms: List<&2, L.Name>, ts: List<&2, M.Cli>) -> List<&2, T.Sect>:
  List.append(&2, T.Sect, L.names.sects(nms), L.tool.sects(ts))

# a tool's source as the lock gives it back: the lock does not write
# `vendor` or a hub name, and eztoml reads a git source with no root as rooted
# at `.` and one with no url as the hub. Law vocabulary.
def source.canon(source: M.Source) -> M.Source:
  match source:
    case M.Hub{_named}:
      M.Hub{""}
    case M.Git{url, rev, tag, root, nar, _vend}:
      +u = url
      M.source.go(String.is_empty(u), u, rev, tag, M.root.or(root), nar, False{})
    case M.Member{_path, _named}:
      M.Hub{""}

# a tool pin as the lock gives it back
def tool.canon(pin: M.Cli) -> M.Cli:
  M.Cli{n, e, b, s} = pin
  M.Cli{n, e, b, source.canon(s)}

# every tool pin, so
def tools.canon(ts: List<&2, M.Cli>) -> List<&2, M.Cli>:
  match ts:
    case []:
      []
    case h <> t:
      tool.canon(h) <> tools.canon(t)

# a package as a lock gives it back: its files in path order, each once. Law
# vocabulary.
def canon.one(pack: L.Pack) -> L.Pack:
  L.Pack{h, s, f} = pack
  L.Pack{h, s, K.files_of(f)}

# every package, so
def canon.all(ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match ps:
    case []:
      []
    case h <> t:
      canon.one(h) <> canon.all(t)

# the packages a lock gives back: in hash order, each with its files in path
# order and each once
def canon(ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  canon.all(L.pack.sort(ps))

# ---------------------------------------------------------------------------
# where a whole-workspace command runs (laws/WorkspaceRootFound.bend)

# a list with its first `count` words dropped, the count looked at first.
# Law vocabulary: ez never calls it.
def past(count: Nat, xs: List<&2, String>) -> List<&2, String>:
  match count:
    case 0n:
      xs
    case 1n+kk:
      match xs:
        case []:
          []
        case _hd <> tl:
          past(kk, tl)
