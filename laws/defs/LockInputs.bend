# the file sets, ledger reads, pins and packages the lock and upgrade laws are
# stated over
import Base
import ../../src/pkg/pkg.bend as K
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/ignore.bend as I
import ../../src/ledger/upgrade.bend as U
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/lock/lock.bend as L
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../src/ws/workspace.bend as WWorkspace
import ../../src/ws/root.bend as RRoot

# a file put at a chosen place in a list: as many files pass in front of it as
# the number says, and it lands at the end when the list runs out first. This
# and `perm` below are the vocabulary the order-independence law needs and
# nothing else uses: ez never calls them, and they say here what a rearranged
# file list is in a form Bend can walk.
def files.perm.ins_at(place: Nat, file: K.Item, xs: List<&2, K.Item>) -> List<&2, K.Item>:
  match place xs:
    case 0n _:
      file <> xs
    case 1n+p Nil{}:
      [file]
    case 1n+p Con{h, t}:
      h <> files.perm.ins_at(p, file, t)

# a list rearranged: each file is taken in turn and put back at the place its
# number names. This is what "the order the walk found them in" means here: a
# filesystem walk is one order and any other walk is another, and the numbers
# say how to get from the one to the other. The encoding is the Lehmer one, so
# the numbers reach every rearrangement of a list and nothing but its
# rearrangements — that is a fact about this encoding and is argued, not
# proved, since the laws below quantify over the numbers and never need it.
def files.perm(ns: List<&2, Nat>, xs: List<&2, K.Item>) -> List<&2, K.Item>:
  match ns xs:
    case Nil{} Nil{}:
      []
    case Nil{} Con{h, t}:
      h <> t
    case Con{n, ms} Nil{}:
      []
    case Con{n, ms} Con{h, t}:
      files.perm.ins_at(n, h, files.perm(ms, t))

# whether a file's path is none of the paths a list holds
def file.fresh(+file: K.Item, xs: List<&2, K.Item>) -> Bool:
  match xs:
    case []:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(String.eq(K.file.at(file), K.file.at(h))), file.fresh(file, t))

# whether a list names each path at most once. A package's file set does: a
# path is a file's identity here, and the walk reads a file once. Two entries
# of the same path but different sha256s are not a package, and the laws below
# say nothing about such a list, because there is nothing true to say: `dedup`
# keeps the last of a run, so which of the two survives is the order's to
# decide.
def files.distinct(xs: List<&2, K.Item>) -> Bool:
  match xs:
    case []:
      True{}
    case Con{+h, +t}:
      Bool.and(file.fresh(h, t), files.distinct(t))

# whether a hash holds neither `/` nor a newline
def plain(+hash: String) -> Bool:
  Bool.and(Str.clear(hash, '/'), Str.clear(hash, '\n'))

# The planner (plan.bend) over the World (world.bend). Every law below is
# about what `ez lock` does, stated over the plan it returns; one with a
# premise that the args say no `--upgrade` is about a plain lock only. The
# interpreter that executes the plan is trusted in src/ez/app.bend.

# what a plan leaves at the lock's path, from what the planner decided. Law
# vocabulary: ez never calls it.
def put.doc(doc: P.Doc) -> P.Wrote:
  match doc:
    case P.Doc{text}:
      P.Put{text}
    case P.Stop{_why}:
      P.Kept{}

# a package with the source the ledger records for its hash. Law vocabulary:
# ez never calls it.
def pinned(+orgs: List<&2, L.Origin>, pack: L.Pack) -> L.Pack:
  L.Pack{+hash, _src, files} = pack
  L.Pack{hash, L.origin(orgs, hash), files}

# every package, so
def pinned.all(+orgs: List<&2, L.Origin>, ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match ps:
    case []:
      []
    case h <> t:
      pinned(orgs, h) <> pinned.all(orgs, t)

# a dependency kept in front of the rest when it is named, else the rest
def deps.put(hit: Bool, dep: M.Dep, rest: List<&2, M.Dep>) -> List<&2, M.Dep>:
  match hit:
    case True{}:
      dep <> rest
    case False{}:
      rest

# every dependency a ledger names `name`, in its order
def deps.named(ds: List<&2, M.Dep>, +name: String) -> List<&2, M.Dep>:
  match ds:
    case []:
      []
    case +h <> t:
      deps.put(String.eq(M.dep.name(h), name), h, deps.named(t, name))

# a tool kept in front of the rest when it is named, else the rest
def tools.put(hit: Bool, pin: M.Tool, rest: List<&2, M.Tool>) -> List<&2, M.Tool>:
  match hit:
    case True{}:
      pin <> rest
    case False{}:
      rest

# every tool a ledger names `name`, in its order
def tools.named(ts: List<&2, M.Tool>, +name: String) -> List<&2, M.Tool>:
  match ts:
    case []:
      []
    case +h <> t:
      tools.put(String.eq(M.tool.name(h), name), h, tools.named(t, name))

# the ledger with nothing but what `--package name` names: the package's own
# fields, and every dependency and tool of that name. Law vocabulary: ez never
# calls it.
def alone(ledger: M.Read, +name: String) -> M.Read:
  match ledger:
    case M.Bad{why}:
      M.Bad{why}
    case M.Good{m}:
      M.Manifest{pn, pe, pb, hub, hubpa, hubpv, ds, ts} = m
      M.Good{M.Manifest{pn, pe, pb, hub, hubpa, hubpv, deps.named(ds, name), tools.named(ts, name)}}

# Idempotence. A plain lock that succeeds writes ez.lock.toml and lays under
# BEND_LIB every tree a clone answered and the planner passed. It writes no
# ledger and no source, and neither file it writes is a tracked `.bend`
# file, so the next lock reads the same ledger and the same committed
# sources. What changes is how the laid trees arrive: from BEND_LIB now,
# with the bytes that were laid. The remotes are taken not to change between
# the two runs, so every other answer is what it was. That a laid tree reads
# back as the manifest and texts it was laid from is the interpreter's side
# (trusted in src/ez/app.bend): a clone's answer carries the manifest its
# files render to, which is the manifest a lay writes.

# whether a verdict passed every check
def passed(verdict: W.Verdict) -> Bool:
  match verdict:
    case W.Ok{_fs, _ss}:
      True{}
    case W.No{_why}:
      False{}
    case W.Named{_names}:
      False{}

# The lock document reads back, trusted in src/lock/lock.bend: a round trip
# through the pinned eztoml reader: the text `ez lock` writes, parsed, gives
# back the packages, the hub and the tool pins it was written from. The
# reader trims every line and strips the quotes off every value; these two
# laws are the first step: a quoted value survives both, whatever it holds.

# What an upgrade writes around the ledger
# (laws/GitignoreAllowlistIsLedger.bend's `ez lock --upgrade` half,
# laws/UpgradeRewritesImports.bend, laws/RewriteKeepsOtherLines.bend). The
# upgrade writes `.gitignore` as `I.sync` makes it from the file it read
# over the dependencies it leaves, and each source it read with every moved
# hash rewritten (`U.reimport.many`), when that changes it. The laws below
# say so of the plan, `P.put`, and the laws of
# laws/GitignoreAllowlistIsLedger.bend and laws/RewriteKeepsOtherLines.bend
# say what `I.sync` and `U.reimport.many` do to a text. A source is one the
# interpreter listed, a `.bend` file outside `.ez` and `.git`; the laws take
# the ones the upgrade read, and a path the World names once, as the
# interpreter lists each file once.

# what the upgrade decides on a World. Law vocabulary: ez never calls it.
def next.of(world: W.World) -> Up.Next:
  W.World{args, +ledger, _listing, _replies, ups} = world
  W.next(args, ledger, ups)

# the sources it read
def found(world: W.World) -> List<&2, Up.Found>:
  Up.next.found(next.of(world))

# the dependencies of a ledger model, none when it did not parse
def ledger.deps(read: M.Read) -> List<&2, M.Dep>:
  match read:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _hpa, _hpv, ds, _ts} = m
      ds

# The upgrade's moves. `ez lock --upgrade` asks the remote about each
# selected pin with a commit: one with a tag re-resolves the tag (a `Refs`
# answer, read by `Up.follow`), and one with only a commit follows the
# default branch (a `Head` answer, read by `Up.forward`). Either moves only
# to a commit the remote says descends from the pin (an `Above` answer, read
# by `Up.onward`). The laws are stated over `P.ledger.next`, the ledger
# model the upgrade renders into ez.toml, which is ez.toml as it was when
# the upgrade refuses, and what the file's bytes read back as
# (`upgrade_reads_back`), so they hold of the bytes. That the remote's
# answers are true of the repository is trusted in src/git/git.bend. Law
# vocabulary: ez never calls it.

# the answers to the upgrade's questions a World holds
def ups(world: W.World) -> List<&2, Up.Reply>:
  W.World{_args, _ledger, _listing, _replies, ups} = world
  ups

# the source ez.toml records for the dependency named `n`
def pin(world: W.World, name: String) -> M.Source:
  M.source.dep(W.dep(world, name))

# whether the remote said a commit descends from the pin
def onward.yes(asc: Up.Asc) -> Bool:
  match asc:
    case Up.Asc{yes}:
      yes
    case Up.AscWait{_ask}:
      False{}
    case Up.AscNo{_why}:
      False{}

# whether `rev` is the commit the remote named, and the remote said that
# commit descends from `pin`
def moved.onto(tip: Up.Tip, +rs: List<&2, Up.Reply>, +url: String, +pin: String, +rev: String) -> Bool:
  match tip:
    case Up.At{+to, _tag, _branch}:
      Bool.and(String.eq(rev, to), onward.yes(Up.onward(rs, Up.Above{url, pin, to})))
    case Up.TipWait{_ask}:
      False{}
    case Up.TipNo{_why}:
      False{}

# whether `new` is `old` kept or moved along its history: a pin from a
# repository still, with the tag `old` had, at `old`'s commit or at the commit
# `tip` names when the remote said it descends from `old`'s
def moved.ok(tip: Up.Tip, +rs: List<&2, Up.Reply>, +old: M.Dep, +new: M.Dep) -> Bool:
  Bool.and(Bool.and(M.source.is_git(M.source.dep(new)),
      String.eq(M.source.tag(M.source.dep(new)), M.source.tag(M.source.dep(old)))),
    Bool.or(String.eq(M.source.rev(M.source.dep(new)), M.source.rev(M.source.dep(old))),
      moved.onto(tip, rs, M.source.url(M.source.dep(old)), M.source.rev(M.source.dep(old)),
        M.source.rev(M.source.dep(new)))))

# laws/PathTargetRecordedAsGiven.bend for `ez lock` and `ez lock --upgrade`:
# a source is recorded as the ledger gives it, and every question git is
# asked about it names it anchored at the project, as the planner computes
# it. The directory the lock runs in, which is the project root, is
# `W.args.here`.

# the origins of the ledger the lock is made from: ez.toml's for a plain
# lock, the ledger the upgrade leaves for `--upgrade`
def origins(world: W.World) -> List<&2, L.Origin>:
  W.next.origins(next.of(world))

# whether a ledger parsed
def ledger.good(read: M.Read) -> Bool:
  match read:
    case M.Bad{_why}:
      False{}
    case M.Good{_m}:
      True{}

# whether a directory's ledger says nothing of a workspace: it has none, or it
# has no `[workspace]` table
def quiet.read(rd: WWorkspace.Read) -> Bool:
  match rd:
    case WWorkspace.Lone{}:
      True{}
    case WWorkspace.Bad{_why}:
      False{}
    case WWorkspace.Root{_spec}:
      False{}

# whether a directory read says nothing of a workspace
def quiet.one(text: Maybe<&2, String>) -> Bool:
  match text:
    case None{}:
      True{}
    case Some{tt}:
      quiet.read(WWorkspace.spec.of(tt))

# whether no directory read says anything of a workspace
def quiet(ups: List<&2, RRoot.Up>) -> Bool:
  match ups:
    case []:
      True{}
    case RRoot.Up{_ds, _rs, tx} <> tl:
      Bool.and(quiet.one(tx), quiet(tl))
