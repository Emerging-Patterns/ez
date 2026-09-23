# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import ./up.bend as Up
import ../manifest/manifest.bend as M
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../pkg/pkg.bend as K
import ../pkg/LAWS.bend as KL

# LAW: a package resolves to the origin recorded for it, whatever origins
# follow. A second record of the same hash never shadows the first, so the
# ledger is read the way it was written.
law origin_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.origin(L.Origin{h, s} <> rest, h) == s : L.Src}

# LAW: a package the ledger records is named, whatever it records after it.
# Only a package no record names is fetched from the hub on nothing but its
# hash, and so only such a package can stop a lock for being unnamed.
law known_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.known(L.Origin{h, s} <> rest, h) == True{} : Bool}

# LAW: a fetched checkout whose NAR hash is the one the ledger records passes,
# and the lock goes on to lay it out.
law nar_why_agrees:
  for +n: String
  for url: String
  for rev: String
  for f: {False{} == String.is_empty(n) : Bool}
  {L.nar.why(n, n, url, rev) == "" : String}

# LAW: one whose NAR hash is any other is refused. The reason is never empty,
# and an empty reason is the only one `fetch.judge` lets through.
law nar_why_refuses:
  for +want: String
  for +got: String
  for url: String
  for rev: String
  for f: {False{} == String.is_empty(want) : Bool}
  for d: {False{} == String.eq(want, got) : Bool}
  {String.is_empty(L.nar.why(want, got, url, rev)) == False{} : Bool}

# LAW: and a ledger that records no NAR hash has nothing to check a checkout
# against, so the checkout is refused whatever it hashes to
law nar_why_needs_a_hash:
  for got: String
  for url: String
  for rev: String
  {String.is_empty(L.nar.why("", got, url, rev)) == False{} : Bool}

# The rest of the lock document: the order packages are written in, the
# `0x` name an import carries, and that a lock that was written reads
# back as the lock it was. A lock that names packages in walk order
# instead of hash order is a different file on every machine, and an
# import that kept the path as part of the hash is a package the hub
# has never seen.

# whether a string holds no `/`, and so is one component of a spec
def slashless(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(Char.is_eq(h, '/')), slashless(t))

# LAW: an import names the package before its first slash. The hash is
# the first component, and everything after the slash is the path
# inside the package.
law spec_hash:
  for +h: String
  for +rest: String
  for +e: {slashless(h) == True{} : Bool}
  {L.spec.hash(String.append(h, SCon{'/', rest})) == h : String}

# LAW: a package that sorts at or before the head of a list already in
# order is written first. Insertion is what puts packages in hash
# order, so a lock is the same text however the walk found them.
law pack_ins_le:
  for +x: L.Pack
  for +h: L.Pack
  for t: List<&2, L.Pack>
  for e: {True{} == L.pack.le(x, h) : Bool}
  {L.pack.ins(h <> t, x) == x <> (h <> t) : List<&2, L.Pack>}

# LAW: a lock names the hub it was resolved against, whatever packages
# it holds.
law lock_names_hub:
  for +hub: String
  for ps: List<&2, L.Pack>
  {L.lock.hub(L.doc(hub, ps)) == hub : String}

# The order a lock is written in. pkg says what a rearranged file list is,
# with `perm` and `distinct`; these say the same of a package list, in the
# same shape, so that a package list rearranged is its blocks rearranged.
# Law vocabulary: ez never calls them.

# a package put at a chosen place in a list, as pkg's `perm.ins_at` puts a
# file
def perm.ins_at(place: Nat, pack: L.Pack, ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match place ps:
    case 0n _:
      pack <> ps
    case 1n+p Nil{}:
      [pack]
    case 1n+p Con{h, t}:
      h <> perm.ins_at(p, pack, t)

# a package list rearranged, as pkg's `perm` rearranges a file list: the
# numbers reach every order the walk could have found the packages in
def perm(ns: List<&2, Nat>, ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match ns ps:
    case Nil{} Nil{}:
      []
    case Nil{} Con{h, t}:
      h <> t
    case Con{n, ms} Nil{}:
      []
    case Con{n, ms} Con{h, t}:
      perm.ins_at(n, h, perm(ms, t))

# whether a hash is none of the hashes a package list holds
def hash.fresh(+hash: String, ps: List<&2, L.Pack>) -> Bool:
  match ps:
    case []:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(String.eq(hash, L.pack.hash(h))), hash.fresh(hash, t))

# whether a package list names each hash at most once. The walk's does: it
# passes over a hash it has resolved already.
def distinct(ps: List<&2, L.Pack>) -> Bool:
  match ps:
    case []:
      True{}
    case Con{+h, +t}:
      Bool.and(hash.fresh(L.pack.hash(h), t), distinct(t))

# LAW: the lock's text does not depend on the order the packages were found
# in. Packages are written in hash order, so any rearrangement of a list that
# names each hash once writes the same bytes, tools and hub alike.
# EZ-DOC-2
law lock_order_free:
  for +ns: List<&2, Nat>
  for +ps: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for dis: {distinct(ps) == True{} : Bool}
  {L.render.tools(ts, hub, perm(ns, ps)) == L.render.tools(ts, hub, ps) : String}

# LAW: and a package's block, the text the lock holds for it, does not depend
# on the order its files were found in. Files are written in path order, so
# any rearrangement of a file list that names each path once writes the same
# block. This is pkg's `sort_perm` under `pack.block`.
# EZ-DOC-2
law pack_order_free:
  for +ns: List<&2, Nat>
  for +hash: String
  for +src: L.Src
  for +fs: List<&2, K.File>
  for dis: {KL.distinct(fs) == True{} : Bool}
  {L.pack.block(L.Pack{hash, src, KL.perm(ns, fs)})
    == L.pack.block(L.Pack{hash, src, fs}) : K.File}

# LAW: a lock with no tools is the lock `render` writes. Packages do not
# move because a tool list was empty.
law render_keeps_packages_without_tools:
  for +hub: String
  for ps: List<&2, L.Pack>
  {L.render.pick(True{}, hub, ps, []) == L.render(hub, ps) : String}

# What the lock may hold. The pinned eztoml reader cuts a pair line at its
# first `=`, even inside a quoted key
# (https://github.com/Emerging-Patterns/eztoml/issues/24), so a file path
# holding one would read back as another path. The planner refuses such a
# lock rather than write one that does not read back.

# LAW: a package list with a file whose path holds `=` is not lockable,
# whatever else it holds
law path_eq_unlockable:
  for +hash: String
  for +src: L.Src
  for +at: String
  for +sum: String
  for +fs: List<&2, K.File>
  for +rest: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for e: {False{} == P.path.eqless(at) : Bool}
  {P.lockable(L.Pack{hash, src, K.File{at, sum} <> fs} <> rest, ts, hub) == False{}
    : Bool}

# LAW: and the refusal names the package and the path, so the author knows
# which file to rename
law path_eq_named:
  for +hash: String
  for +src: L.Src
  for +at: String
  for +sum: String
  for +fs: List<&2, K.File>
  for +rest: List<&2, L.Pack>
  for +e: {False{} == P.path.eqless(at) : Bool}
  {P.lockable.why(L.Pack{hash, src, K.File{at, sum} <> fs} <> rest)
    == P.path.eq.why(hash, at) : String}

# The planner (plan.bend) over the World (world.bend). Every law below is
# about what `ez lock` does, stated over the plan it returns; one with a
# premise that the args say no `--upgrade` is about a plain lock only. The
# interpreter that executes the plan is EZ-TRUST-2.

# what a plan leaves at the lock's path, from what the planner decided. Law
# vocabulary: ez never calls it.
def put.doc(doc: P.Doc) -> P.Wrote:
  match doc:
    case P.Doc{text}:
      P.Put{text}
    case P.Stop{_why}:
      P.Kept{}

# LAW: the lock depends on nothing in a World but its Inputs: the ledger it is
# made from (ez.toml, or the one an upgrade leaves), the upgrade's refusal,
# the committed sources, and the verdict on every answer. Two Worlds that agree on
# those write the same bytes to ez.lock.toml, or both write none, however they
# differ otherwise.
# EZ-DOC-3
law lock_reproducible:
  for w1: W.World
  for w2: W.World
  for e: {W.inputs(w1) == W.inputs(w2) : W.Inputs}
  {P.put(w1, "ez.lock.toml") == P.put(w2, "ez.lock.toml") : P.Wrote}

# LAW: a working checkout, whose git trees are read from BEND_LIB, writes the
# lock a fresh clone writes, which has none there and clones and weighs each
# one at its pinned rev, so long as git hands the clone the same bytes.
# EZ-DOC-3
law clone_reproduces:
  for +w: W.World
  {P.put(W.reclone(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: a plain lock never writes ez.toml
# EZ-DOC-5
law plain_lock_keeps_ledger:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.put(w, "ez.toml") == P.Kept{} : P.Wrote}

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

# LAW: every package a plain lock resolves, and so every package its lock
# renders, carries the source ez.toml records for its hash. Tools are
# rendered from the ledger's `[tools.*]` alone, as `M.tools_of` reads them.
# EZ-DOC-5
law plain_lock_pins_ledger_sources:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {pinned.all(W.origins(W.ledger.of(w)), P.packs(w)) == P.packs(w)
    : List<&2, L.Pack>}

# LAW: `ez lock` that refuses, plain or `--upgrade`, writes, lays and removes
# nothing: not the lock, not ez.toml, `.gitignore` or a source, and no tree.
# Its plan has no effect at all; the reason is how it ends. An upgrade whose
# remote answers refuse it, or whose lock then refuses, is such a World.
# EZ-OUT-2
law lock_refusal_writes_nothing:
  for +w: W.World
  for r: {P.refuses(w) == True{} : Bool}
  {P.writes(P.plan(w)) == False{} : Bool}

# The upgrade's decisions (lock/up.bend) are stated over `P.ledger.next`, the
# ledger model an upgrade renders into ez.toml, and over the questions it asks,
# `P.wants.up`. A plain lock is the World whose args say no `--upgrade`, and it
# is what these two say it is.

# LAW: a plain lock asks no upgrade question, so it asks a remote nothing but
# the tree at a rev the ledger already pins
law plain_lock_asks_no_upgrade:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.wants.up(w) == [] : List<&2, Up.Ask>}

# LAW: and the ledger a plain lock leaves is ez.toml as it is
law plain_lock_ledger_next:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.ledger.next(w) == W.parsed(W.ledger.of(w)) : M.Read}

# LAW: a tree read from BEND_LIB is judged exactly as the same bytes cloned
# at the pinned rev and weighed to the ledger's narHash
law lib_judged_as_clone:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept(orgs, hub, hash, W.Got{W.Lib{}, manifest, ss})
    == W.accept(orgs, hub, hash,
      W.Got{W.Clone{L.src.nar(L.origin(orgs, hash))}, manifest, ss})
    : W.Verdict}

# LAW: every package the walk resolves carries the source the ledger records
# for its hash, one step at a time
law walk_pins_ledger_sources:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {pinned.all(orgs, P.walk.packs(P.walk(fuel, orgs, js, wk)))
    == P.walk.packs(P.walk(fuel, orgs, js, wk)) : List<&2, L.Pack>}

# LAW: the walk resolves each hash at most once, one step at a time: a step
# passes over a hash it has already resolved
law walk_keeps_hashes_distinct:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {distinct(P.walk.packs(wk)) == True{} : Bool}
  {distinct(P.walk.packs(P.walk(fuel, orgs, js, wk))) == True{} : Bool}

# LAW: so every package list plain `ez lock` resolves, which is the list its
# lock renders, names each hash once. That is `lock_order_free`'s premise,
# so the lock ez writes does not depend on the order the walk found its
# packages in.
# EZ-DOC-2
law plain_lock_hashes_distinct:
  for w: W.World
  {distinct(P.packs(w)) == True{} : Bool}

# LAW: a tracked path under `.ez/` is never a root of the lock. The trees
# there are packages, read as packages, and not the project's own sources.
law root_skips_ez:
  for +p: String
  for text: String
  {P.roots.one(W.Source{".ez/" ++ p, text}) == [] : List<&2, String>}

# Idempotence. A plain lock that succeeds writes ez.lock.toml and lays under
# BEND_LIB every tree a clone answered and the planner passed. It writes no
# ledger and no source, and neither file it writes is a tracked `.bend` file,
# so the next lock reads the same ledger and the same committed sources. What
# changes is how the laid trees arrive: from BEND_LIB now, with the bytes that
# were laid. The remotes are taken not to change between the two runs, so
# every other answer is what it was. That a laid tree reads back as the
# manifest and texts it was laid from is the interpreter's side (EZ-TRUST-2):
# a clone's answer carries the manifest its files render to, which is the
# manifest a lay writes.

# whether a verdict passed every check
def passed(verdict: W.Verdict) -> Bool:
  match verdict:
    case W.Ok{_fs, _ss}:
      True{}
    case W.No{_why}:
      False{}

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
      after.clone(passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
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

# the World a plain lock leaves, for the next lock to read. Law vocabulary: ez
# never calls it.
def after(+world: W.World) -> W.World:
  after.pick(P.refuses(world), world)

# the hash of an answer a clone gave that passed every check: a tree the next
# plan would lay
def fresh.how(
  how: W.How,
  +orgs: List<&2, L.Origin>,
  +hub: String,
  +hash: String,
  +manifest: String,
  +ss: List<&2, String>
) -> List<&2, String>:
  match how:
    case W.Lib{}:
      []
    case W.Clone{+got}:
      Bool.pick(List<&2, String>,
        passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})), [hash], [])
    case W.Served{}:
      []

def fresh.one(+orgs: List<&2, L.Origin>, +hub: String, +hash: String, answer: W.Answer) -> List<&2, String>:
  match answer:
    case W.Miss{_why}:
      []
    case W.Got{how, manifest, ss}:
      fresh.how(how, orgs, hub, hash, manifest, ss)

def fresh.all(+orgs: List<&2, L.Origin>, +hub: String, rs: List<&2, W.Reply>) -> List<&2, String>:
  match rs:
    case []:
      []
    case W.Reply{ask, answer} <> t:
      +hash = W.ask.hash(ask)
      List.append(&2, String, fresh.one(orgs, hub, hash, answer), fresh.all(orgs, hub, t))

# every tree a World's clones answered that passed every check. In a World
# that asks about each hash once, which is every World the interpreter
# gathers, these are the trees a plain lock that succeeds lays (`P.lays` over
# `P.cloned`). Law vocabulary: ez never calls it.
def fresh(world: W.World) -> List<&2, String>:
  W.World{+args, +ledger, _listing, replies, +ups} = world
  fresh.all(W.next.origins(W.next(args, ledger, ups)),
    W.next.hub(W.next(args, ledger, ups)), replies)

# LAW: plain `ez lock` is idempotent. Run again on the World it leaves, it
# writes the same bytes to ez.lock.toml, or, when it refused, refuses again
# and writes none. A laid tree read from BEND_LIB is judged as the clone that
# passed was, which is `clone_reproduces` read backwards.
# EZ-DOC-4
law lock_idempotent:
  for +w: W.World
  {P.put(after(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: and it lays nothing new. On the World a lock that succeeded leaves, no
# tree arrives by a clone that passes, so every tree the next lock reads that
# passes was read from BEND_LIB or served by the hub, and none is laid again.
# EZ-DOC-4
law relock_lays_nothing:
  for +w: W.World
  for ok: {P.refuses(w) == False{} : Bool}
  {fresh(after(w)) == [] : List<&2, String>}

# The lock document. EZ-DOC-1 is a round trip through eztoml's reader, and
# the reader trims every line and strips the quotes off every value. These two
# laws are its first step: a quoted value survives both, whatever it holds.

# LAW: a quoted value is already trimmed. Its first and last characters are
# quotes, so no space it holds is at an end.
law trim_quoted:
  for +v: String
  {T.trim(T.quote(v)) == T.quote(v) : String}

# LAW: and stripping the quotes off gives the value back, even one that holds
# quotes of its own
law strip_quoted:
  for +v: String
  {T.strip(T.quote(v), '"', '"') == v : String}
