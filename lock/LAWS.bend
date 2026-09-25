# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import ./up.bend as Up
import ../manifest/upgrade.bend as U
import ../manifest/manifest.bend as M
import ../toml/toml.bend as T
import ../pkg/pkg.bend as K
import ../pkg/LAWS.bend as KL
import ../hub/hub.bend as Web
import ../manifest/upgrade.bend as U
import ../manifest/ignore.bend as I
import ../manifest/LAWS.bend as ML
import ../check/str.bend as Str

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
  for +nms: List<&2, L.Name>
  for +ps: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for dis: {distinct(ps) == True{} : Bool}
  {L.render.names(nms, ts, hub, perm(ns, ps)) == L.render.names(nms, ts, hub, ps) : String}

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

# LAW: `ez lock`, plain or `--upgrade`, ends with the status of its plan's
# outcome, which is 1 exactly when it refuses and 0 when it does not
# EZ-OUT-1
law lock_exits_as_it_refuses:
  for +w: W.World
  {P.code(P.plan(w)) == P.status.of(P.refuses(w)) : U32}

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

# What `ez lock --upgrade` keeps and what it asks about. These laws are stated
# over `P.ledger.next`, the ledger model the upgrade renders into ez.toml,
# which is what the file's bytes read back as (`upgrade_reads_back`, EZ-LED-4),
# so they hold of the bytes. Whatever the remote
# answered, and on every round of questions, the model keeps the entries these
# name. `W.dep(w, n)` is the dependency ez.toml records under `n`, as `M.dep`
# finds it, the first of that name.

# the tool a ledger pins under a name, as `M.tool.find` finds it. Law
# vocabulary: ez never calls it.
def tool.at(ledger: M.Read, name: String) -> M.Tool:
  M.tool.find(M.tools_of(ledger), name)

# the upgrade's answers a World holds
def ups.of(world: W.World) -> List<&2, Up.Reply>:
  W.World{_args, _ledger, _listing, _replies, ups} = world
  ups

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

# LAW: `ez lock --upgrade` never moves a hub dependency. The entry ez.toml
# records under a name, when its source is the hub, is the entry the ledger
# the upgrade leaves records under that name, whatever `--package` named and
# whatever the remote said. A hub package's hash is its pin.
# EZ-RES-4
law upgrade_holds_hub:
  for +w: W.World
  for +n: String
  for hub: {M.source.is_git(M.source.dep(W.dep(w, n))) == False{} : Bool}
  {M.dep(P.ledger.next(w), n) == W.dep(w, n) : M.Dep}

# LAW: `--package n` leaves every dependency of another name as ez.toml has
# it: its rev, tag, hash, and every other field
# EZ-RES-6
law upgrade_one_frames_deps:
  for +w: W.World
  for +n: String
  for +m: String
  for e: {W.args.only(w) == n : String}
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {M.dep(P.ledger.next(w), m) == W.dep(w, m) : M.Dep}

# LAW: and every tool of another name
# EZ-RES-6
law upgrade_one_frames_tools:
  for +w: W.World
  for +n: String
  for +m: String
  for e: {W.args.only(w) == n : String}
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {tool.at(P.ledger.next(w), m) == tool.at(W.parsed(W.ledger.of(w)), m) : M.Tool}

# LAW: and `ez lock --upgrade --package n` asks the remote exactly what it
# asks of a ledger holding nothing but the entries named `n`, on every round
# of questions. Refs, the default branch, tags, ancestry and checkouts are
# asked of those entries alone; no other dependency or tool reaches the
# remote, or changes a question that is asked.
# EZ-RES-6
law upgrade_one_asks_alone:
  for +w: W.World
  for +n: String
  for u: {W.args.upgrade(w) == True{} : Bool}
  for e: {W.args.only(w) == n : String}
  for ne: {String.is_empty(n) == False{} : Bool}
  {P.wants.up(w) == Up.next.asks(Up.next(n, alone(W.parsed(W.ledger.of(w)), n), ups.of(w)))
    : List<&2, Up.Ask>}

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
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {pinned.all(orgs, P.walk.packs(P.walk(fuel, orgs, ns, js, wk)))
    == P.walk.packs(P.walk(fuel, orgs, ns, js, wk)) : List<&2, L.Pack>}

# LAW: the walk resolves each hash at most once, one step at a time: a step
# passes over a hash it has already resolved
law walk_keeps_hashes_distinct:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {distinct(P.walk.packs(wk)) == True{} : Bool}
  {distinct(P.walk.packs(P.walk(fuel, orgs, ns, js, wk))) == True{} : Bool}

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

# The import scan. A root of the lock is a line bend's loader reads as an
# import of a hub package. The loader trims each line of a file's header and
# splits an import at its runs of white space, so what stands between
# `import`, the path, `as` and the name may be any run of spaces and tabs, and
# the line may be indented and may trail blanks.

# a character of a run of white space in an import line
type Gap is Data:
  Sp{}
  Tab{}

# the character a gap stands for
def gap.char(one: Gap) -> Char:
  match one:
    case Sp{}:
      ' '
    case Tab{}:
      '\t'

# a run of spaces and tabs as text
def gap(gs: List<&2, Gap>) -> String:
  match gs:
    case []:
      ""
    case g <> t:
      SCon{gap.char(g), gap(t)}

# whether a string holds no white space, as the path and the name of an
# import do
def solid(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(K.blank(h)), solid(t))

# an import of a hub package as a line of a source file: its indentation,
# `import`, a run of spaces and tabs, `0x<hash>/<path>`, a run, `as`, a run,
# the name, and the blanks that trail it
def hub.line(
  lead: List<&2, Gap>,
  one: List<&2, Gap>,
  hash: String,
  path: String,
  two: List<&2, Gap>,
  three: List<&2, Gap>,
  name: String,
  tail: List<&2, Gap>
) -> String:
  gap(lead) ++ ("import" ++ (gap(one) ++ (("0x" ++ (hash ++ SCon{'/', path}))
    ++ (gap(two) ++ ("as" ++ (gap(three) ++ (name ++ gap(tail))))))))

# LAW: a line bend reads as an import of a hub package names a root of the
# lock, whatever run of spaces and tabs stands between `import` and the path,
# the path and `as`, and `as` and the name, however the line is indented and
# whatever blanks trail it, so long as the lines above it leave the header
# open, and whatever lines follow it. `ez doctor` reads the same roots.
# EZ-DOC-3
law root_reads_as_bend:
  for +at: String
  for +text: String
  for +pre: List<&2, String>
  for +post: List<&2, String>
  for +ms: List<&2, String>
  for +fs: List<&2, String>
  for +lead: List<&2, Gap>
  for +o: Gap
  for +os: List<&2, Gap>
  for +hash: String
  for +path: String
  for +w: Gap
  for +ws: List<&2, Gap>
  for +r: Gap
  for +rs: List<&2, Gap>
  for +n: Char
  for +ns: String
  for +tail: List<&2, Gap>
  for ez: {String.starts_with(at, ".ez/") == False{} : Bool}
  for ls: {String.lines(text) == List.append(&2, String, pre,
    hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail) <> post)
    : List<&2, String>}
  for hd: {K.scan.walk(pre, K.Head{True{}, [], []}) == K.Head{True{}, ms, fs} : K.Head}
  for +hp: {slashless(hash) == True{} : Bool}
  for hs: {solid(hash) == True{} : Bool}
  for pp: {solid(path) == True{} : Bool}
  for +np: {solid(SCon{n, ns}) == True{} : Bool}
  {L.seen.holds(P.roots.one(W.Source{at, text}), "0x" ++ hash) == True{} : Bool}

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
    case W.Named{_names}:
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
# the interpreter's side (EZ-TRUST-2).
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
    Up.Reply{Up.Ignore{}, Up.Text{ig.left(Up.next.edits(nx), ig.read(ups))}} <> ups}

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
    case W.Said{_text}:
      []
    case W.Locked{_text}:
      []

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
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.put(after(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: and it lays nothing new. On the World a lock that succeeded leaves, no
# tree arrives by a clone that passes, so every tree the next lock reads that
# passes was read from BEND_LIB or served by the hub, and none is laid again.
# EZ-DOC-4
law relock_lays_nothing:
  for +w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  {fresh(after(w)) == [] : List<&2, String>}

# The lock document reads back. EZ-DOC-1 is a round trip through the pinned
# eztoml reader: the text `ez lock` writes, parsed, gives back the packages,
# the hub and the tool pins it was written from. The reader trims every line
# and strips the quotes off every value; these two laws are the first step: a
# quoted value survives both, whatever it holds.

# What an upgrade writes around the ledger (EZ-VEN-1's `ez lock --upgrade`
# half, EZ-VEN-2, EZ-VEN-3). The upgrade writes `.gitignore` as `I.sync`
# makes it from the file it read over the dependencies it leaves, and each
# source it read with every moved hash rewritten (`U.reimport.many`), when
# that changes it. The laws below say so of the plan, `P.put`, and the laws
# of `manifest/LAWS.bend` say what `I.sync` and `U.reimport.many` do to a
# text. A source is one the interpreter listed, a `.bend` file outside `.ez`
# and `.git`; the laws take the ones the upgrade read, and a path the World
# names once, as the interpreter lists each file once.

# what the upgrade decides on a World. Law vocabulary: ez never calls it.
def up.next(world: W.World) -> Up.Next:
  W.World{args, +ledger, _listing, _replies, ups} = world
  W.next(args, ledger, ups)

# the hashes whose trees the upgrade commits under `.ez/lib`: the vendored
# hashes of the dependencies it leaves
def vends(world: W.World) -> List<&2, String>:
  Up.next.vends(up.next(world))

# the hashes it moved, each with the hash that replaces it in an import
def swaps(world: W.World) -> List<&2, U.Swap>:
  Up.next.swaps(up.next(world))

# the sources it read
def found(world: W.World) -> List<&2, Up.Found>:
  Up.next.found(up.next(world))

# a file's text as the World answered it, "" when it did not
def ignore.said(said: Up.Said) -> String:
  match said:
    case Up.Said{text}:
      text
    case Up.Unsaid{_why}:
      ""
    case Up.Unasked{_ask}:
      ""

# `.gitignore` as the World answered the upgrade
def ignore.read(world: W.World) -> String:
  W.World{_args, _ledger, _listing, _replies, ups} = world
  ignore.said(Up.text.said(ups, Up.Ignore{}))

# whether no source of a list is at a path
def found.miss(fs: List<&2, Up.Found>, +path: String) -> Bool:
  match fs:
    case []:
      True{}
    case Up.Found{at, _text} <> t:
      +rest = found.miss(t, path)
      Bool.and(Bool.not(String.eq(at, path)), rest)

# the dependencies of a ledger model, none when it did not parse
def ledger.deps(read: M.Read) -> List<&2, M.Dep>:
  match read:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _hpa, _hpv, ds, _ts} = m
      ds

# what a path holds after a plan: what the plan wrote there, or what it held
def left.at(wrote: P.Wrote, +before: String) -> String:
  match wrote:
    case P.Kept{}:
      before
    case P.Put{text}:
      text

# LAW: when `ez lock --upgrade` writes `.gitignore`, its allowlist names
# exactly the hashes whose trees the upgrade commits, the vendored hashes of
# the dependencies it leaves, each once. No source the upgrade read is at
# `.gitignore`, and no vendored hash holds a newline.
# EZ-VEN-1
law upgrade_allowlist_is_the_ledger:
  for +w: W.World
  for +text: String
  for put: {P.put(w, ".gitignore") == P.Put{text} : P.Wrote}
  for +miss: {found.miss(found(w), ".gitignore") == True{} : Bool}
  for +ev: {Str.clear.all(vends(w), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(text)) == vends(w) : List<&2, String>}

# LAW: and keeps every line of the `.gitignore` it read that is not ez's,
# byte for byte and in order
# EZ-VEN-1
law upgrade_allowlist_keeps_other_lines:
  for +w: W.World
  for +text: String
  for put: {P.put(w, ".gitignore") == P.Put{text} : P.Wrote}
  for +miss: {found.miss(found(w), ".gitignore") == True{} : Bool}
  for +ev: {Str.clear.all(vends(w), '\n') == True{} : Bool}
  {I.others(I.file.lines(text)) == I.others(I.file.lines(ignore.read(w)))
    : List<&2, String>}

# LAW: and when it writes ez.toml, the hashes it commits are the vendored
# hashes of the ledger model it renders there, `P.ledger.next`, so the
# allowlist is that of the ledger ez.toml reads back as (EZ-LED-4)
# EZ-VEN-1
law upgrade_vends_the_ledger:
  for +w: W.World
  for +text: String
  for put: {P.put(w, "ez.toml") == P.Put{text} : P.Wrote}
  for +miss: {found.miss(found(w), "ez.toml") == True{} : Bool}
  {vends(w) == I.vended(ledger.deps(P.ledger.next(w))) : List<&2, String>}

# LAW: a `.bend` source the upgrade read, once, holds afterwards its text
# with every moved hash rewritten, when `ez lock --upgrade` does not refuse.
# The laws of `manifest/LAWS.bend` say what that rewriting does to the text.
law upgrade_rewrites_sources:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {found.miss(pre, at) == True{} : Bool}
  for +mq: {found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  {left.at(P.put(w, at), text) == U.reimport.many(swaps(w), text) : String}

# LAW: so when an upgrade moves a hash, every line of such a source that
# starts `import <old>/` starts `import <new>/` afterwards, for the moves an
# upgrade makes (`ML.moves.ok`)
# EZ-VEN-2
law upgrade_rewrites_imports:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {found.miss(pre, at) == True{} : Bool}
  for +mq: {found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  for +i: Nat
  for +old: String
  for +new: String
  for +mv: {ML.moves.ok(swaps(w)) == True{} : Bool}
  for +to: {ML.moved.to(swaps(w), old) == Some{new} : Maybe<&2, String>}
  for hit: {String.starts_with(ML.line.at(String.lines(text), i), U.reimport.head(old))
    == True{} : Bool}
  {String.starts_with(ML.line.at(String.lines(left.at(P.put(w, at), text)), i),
    U.reimport.head(new)) == True{} : Bool}

# LAW: and every other line of it is left byte for byte as it was
# EZ-VEN-3
law upgrade_leaves_other_lines:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {found.miss(pre, at) == True{} : Bool}
  for +mq: {found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  for +i: Nat
  for +mv: {ML.moves.ok(swaps(w)) == True{} : Bool}
  for miss: {ML.names.none(swaps(w), ML.line.at(String.lines(text), i)) == True{} : Bool}
  {ML.line.at(String.lines(left.at(P.put(w, at), text)), i)
    == ML.line.at(String.lines(text), i) : String}

# LAW: and no line is added or dropped
# EZ-VEN-3
law upgrade_keeps_line_count:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {found.miss(pre, at) == True{} : Bool}
  for +mq: {found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  for +mv: {ML.moves.ok(swaps(w)) == True{} : Bool}
  {List.length(&2, String, String.lines(left.at(P.put(w, at), text)))
    == List.length(&2, String, String.lines(text)) : Nat}

# LAW: and a source none of whose lines names a moved hash is not written
# EZ-VEN-3
law upgrade_writes_only_hits:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {found.miss(pre, at) == True{} : Bool}
  for +mq: {found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for none: {ML.names.none.all(swaps(w), String.lines(text)) == True{} : Bool}
  {P.put(w, at) == P.Kept{} : P.Wrote}
# That the lock's text reads back as its tables is EZ-DOC-1, trusted through
# eztoml's round trip (EZ-TRUST-8): ez writes it as eztoml's `render` of the
# document it assembles. What is left here is ez's side: what ez reads out of
# the tables, `L.packs`, `L.lock.hub` and `M.tools`, and what it gives back:
# the packages in hash order with their files in path order and each once,
# which is `canon`, and each tool without `vendor`, which the lock does not
# write, which is `tools.canon`. Law vocabulary: ez never calls these.

# the tables a lock renders after its packages: the `[names]` table, when it
# resolved a name, then every tool's table. Law vocabulary.
def tail(nms: List<&2, L.Name>, ts: List<&2, M.Tool>) -> List<&2, T.Sect>:
  List.append(&2, T.Sect, L.names.sects(nms), L.tool.sects(ts))

# the document a lock renders: the `[lock]` table, every package's two tables
# in hash order, then its names and every tool's table. Law vocabulary.
def lock.doc(nms: List<&2, L.Name>, ts: List<&2, M.Tool>, hub: String, ps: List<&2, L.Pack>) -> List<&2, T.Sect>:
  List.append(&2, T.Sect, L.doc(hub, ps), tail(nms, ts))

# a name as a lock gives it back, from the pair it is written as
def name.back(item: K.File) -> L.Name:
  K.File{at, sum} = item
  L.Name{at, sum}

# every name, so
def names.back(fs: List<&2, K.File>) -> List<&2, L.Name>:
  match fs:
    case []:
      []
    case h <> t:
      name.back(h) <> names.back(t)

# a name as a file of a package: its `<name>@<version>` as the path and its
# hash as the sum. Law vocabulary.
def name.as.file(nm: L.Name) -> K.File:
  L.Name{nv, hash} = nm
  K.File{nv, hash}

# every name, so. Law vocabulary.
def names.as.files(nms: List<&2, L.Name>) -> List<&2, K.File>:
  match nms:
    case []:
      []
    case h <> t:
      name.as.file(h) <> names.as.files(t)

# the names a lock gives back: in name order, each once, as the `[names]`
# table sorts them the way a package's files are sorted
def names.canon(nms: List<&2, L.Name>) -> List<&2, L.Name>:
  names.back(K.files_of(names.as.files(nms)))

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

# a tool pin as the lock gives it back
def tool.canon(pin: M.Tool) -> M.Tool:
  M.Tool{n, e, b, s} = pin
  M.Tool{n, e, b, source.canon(s)}

# every tool pin, so
def tools.canon(ts: List<&2, M.Tool>) -> List<&2, M.Tool>:
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

# The upgrade's moves. `ez lock --upgrade` asks the remote about each selected
# pin with a commit: one with a tag re-resolves the tag (a `Refs` answer, read
# by `Up.follow`), and one with only a commit follows the default branch (a
# `Head` answer, read by `Up.forward`). Either moves only to a commit the
# remote says descends from the pin (an `Above` answer, read by `Up.onward`).
# The laws are stated over `P.ledger.next`, the ledger model the upgrade
# renders into ez.toml, which is ez.toml as it was when the upgrade refuses,
# and what the file's bytes read back as (`upgrade_reads_back`), so they hold
# of the bytes. That the remote's
# answers are true of the repository is EZ-RES-7. Law vocabulary: ez never
# calls it.

# the answers to the upgrade's questions a World holds
def ups(world: W.World) -> List<&2, Up.Reply>:
  W.World{_args, _ledger, _listing, _replies, ups} = world
  ups

# the source ez.toml records for the dependency named `n`
def pin(world: W.World, name: String) -> M.Source:
  M.source.dep(W.dep(world, name))

# whether a source is pinned by its commit alone, with no tag
def rev_only.src(src: M.Source) -> Bool:
  match src:
    case M.Hub{_named}:
      False{}
    case M.Git{_url, _rev, tag, _root, _nar, _vend}:
      String.is_empty(tag)

# whether a dependency is pinned by its commit alone
def rev_only(dep: M.Dep) -> Bool:
  rev_only.src(M.source.dep(dep))

# whether a source is pinned through a tag
def tagged.src(src: M.Source) -> Bool:
  match src:
    case M.Hub{_named}:
      False{}
    case M.Git{_url, _rev, tag, _root, _nar, _vend}:
      Bool.not(String.is_empty(tag))

# whether a dependency is pinned through a tag
def tagged(dep: M.Dep) -> Bool:
  tagged.src(M.source.dep(dep))

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
def moved.to(tip: Up.Tip, +rs: List<&2, Up.Reply>, +url: String, +pin: String, +rev: String) -> Bool:
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
      moved.to(tip, rs, M.source.url(M.source.dep(old)), M.source.rev(M.source.dep(old)),
        M.source.rev(M.source.dep(new)))))

# the pin the upgrade leaves for the dependency named `n`, against the one
# ez.toml records and the default branch tip the remote named for it
def forward.ok(+world: W.World, +name: String) -> Bool:
  moved.ok(Up.forward(ups(world), M.source.url(pin(world, name))), ups(world),
    W.dep(world, name), M.dep(P.ledger.next(world), name))

# and against the commit the remote named for its tag
def follow.ok(+world: W.World, +name: String) -> Bool:
  moved.ok(Up.follow(ups(world), M.source.url(pin(world, name)), M.source.tag(pin(world, name))),
    ups(world), W.dep(world, name), M.dep(P.ledger.next(world), name))

# LAW: a dependency pinned by its commit alone moves, if it moves at all, to
# the default branch tip the remote named, and only when the remote said that
# tip descends from the pin; and it stays a commit pin, since it keeps the tag
# it had, which is none. Whatever else the upgrade does, and whether or not it
# refuses.
# EZ-RES-5
law upgrade_forward_moves_onward:
  for +w: W.World
  for +n: String
  for bare: {rev_only(W.dep(w, n)) == True{} : Bool}
  {forward.ok(w, n) == True{} : Bool}

# LAW: and when `ez lock --upgrade` asks about it, and the tip the remote
# names is another commit that the remote says does not descend from the pin,
# the upgrade refuses, so it writes nothing and exits 1 (EZ-OUT-2)
# EZ-RES-5
law upgrade_forward_refuses_off:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +bare: {rev_only(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for head: {Up.forward(ups(w), M.source.url(pin(w, n))) == Up.At{tip, tag, branch} : Up.Tip}
  for moved: {String.eq(M.source.rev(pin(w, n)), tip) == False{} : Bool}
  for off: {Up.onward(ups(w), Up.Above{M.source.url(pin(w, n)), M.source.rev(pin(w, n)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {P.refuses(w) == True{} : Bool}

# LAW: and when `ez lock --upgrade` asks about it and does not refuse, it is
# at the default branch tip the remote named: moved there, or there already
# EZ-RES-5
law upgrade_forward_reaches_tip:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +bare: {rev_only(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for head: {Up.forward(ups(w), M.source.url(pin(w, n))) == Up.At{tip, tag, branch} : Up.Tip}
  for ok: {P.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(M.dep(P.ledger.next(w), n))) == tip : String}

# LAW: a dependency pinned through a tag keeps its tag and moves, if it moves
# at all, to the commit the remote names for that tag, and only when the
# remote said that commit descends from the pin
# EZ-RES-8
law upgrade_tag_follows:
  for +w: W.World
  for +n: String
  for named: {tagged(W.dep(w, n)) == True{} : Bool}
  {follow.ok(w, n) == True{} : Bool}

# LAW: and when `ez lock --upgrade` asks about it, and the tag now names
# another commit that the remote says does not descend from the pin, the
# upgrade refuses
# EZ-RES-8
law upgrade_tag_refuses_off:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +named: {tagged(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for refs: {Up.follow(ups(w), M.source.url(pin(w, n)), M.source.tag(pin(w, n)))
    == Up.At{tip, tag, branch} : Up.Tip}
  for moved: {String.eq(M.source.rev(pin(w, n)), tip) == False{} : Bool}
  for off: {Up.onward(ups(w), Up.Above{M.source.url(pin(w, n)), M.source.rev(pin(w, n)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {P.refuses(w) == True{} : Bool}

# LAW: and when the tag still names the pinned commit, but that commit's
# checkout no longer agrees with the pin, in its hash, its NAR hash or its
# root, the upgrade refuses: the pin drifted
# EZ-RES-8
law upgrade_tag_refuses_drift:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for +nar: String
  for +root: String
  for +manifest: String
  for +srcs: List<&2, String>
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +named: {tagged(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for refs: {Up.follow(ups(w), M.source.url(pin(w, n)), M.source.tag(pin(w, n)))
    == Up.At{tip, tag, branch} : Up.Tip}
  for same: {String.eq(M.source.rev(pin(w, n)), tip) == True{} : Bool}
  for co: {Up.checkout(ups(w), Up.Tree{M.source.url(pin(w, n)), M.source.rev(pin(w, n)),
    M.dep.entry(W.dep(w, n))}) == Up.Co{nar, root, manifest, srcs} : Up.Co}
  for drift: {U.agree(M.dep.hash(W.dep(w, n)), Up.hash.kept(M.dep.hash(W.dep(w, n)), manifest),
    M.source.nar(pin(w, n)),
    nar, M.source.root(pin(w, n)), root) == False{} : Bool}
  {P.refuses(w) == True{} : Bool}

# LAW: and a pin through a tag that `ez lock --upgrade` asks about, when it
# does not refuse, is at the commit the remote names for its tag: the tag is
# re-resolved, not only allowed to be
# EZ-RES-8
law upgrade_tag_resolves:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +named: {tagged(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for refs: {Up.follow(ups(w), M.source.url(pin(w, n)), M.source.tag(pin(w, n)))
    == Up.At{tip, tag, branch} : Up.Tip}
  for ok: {P.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(M.dep(P.ledger.next(w), n))) == tip : String}

# `ez lock --upgrade` is idempotent too. Run again on the World it leaves,
# against a remote that did not change, every pin is at its own tip: the
# second run asks each selected pin's remote the question the first asked,
# gets the tip it moved to, finds the pin at it, and checks the tree out
# again, which agrees with the hash, narHash and root the first run wrote, so
# it keeps the pin. Nothing moves, so it writes no ez.toml, no source and no
# tree, and the lock it writes is the one the first run wrote.
#
# The second run reads ez.toml's bytes, and the ledger the first run wrote
# reads back as the model it rendered, `P.ledger.next` (`upgrade_reads_back`,
# EZ-LED-4). An upgrade that moved nothing wrote no ledger, and reads back as
# it is. The upgrade laws of EZ-RES-4 to 8 are stated over the same model.

# LAW: `ez lock --upgrade`, run again on the World it leaves, writes the same
# bytes to ez.lock.toml, or, when it refused, refuses again and writes none
# EZ-DOC-4
law upgrade_idempotent:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for rb: ML.ReadsBack()
  {P.put(after(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: and it moves nothing: the ledger model it renders is the one the first
# run rendered
# EZ-DOC-4
law reupgrade_moves_nothing:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for rb: ML.ReadsBack()
  {P.ledger.next(after(w)) == P.ledger.next(w) : M.Read}

# LAW: so, after one that succeeded, it does not write ez.toml
# EZ-DOC-4
law upgrade_settles:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for rb: ML.ReadsBack()
  {P.put(after(w), "ez.toml") == P.Kept{} : P.Wrote}

# LAW: and it lays nothing new: every tree the first run laid is read from
# BEND_LIB, and no tree arrives by a clone that passes
# EZ-DOC-4
law reupgrade_lays_nothing:
  for +w: W.World
  for u: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for rb: ML.ReadsBack()
  {fresh(after(w)) == [] : List<&2, String>}

# LAW: and it writes no path but the lock: no ez.toml, no source and no
# `.gitignore`, since the `.gitignore` the first run left is already in sync
# with the ledger it left (`ML.sync_idempotent`), for a ledger whose vendored
# hashes hold no newline, as a `0x` name never does
# EZ-DOC-4
law reupgrade_writes_only_lock:
  for +w: W.World
  for +p: String
  for u: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for ev: {Str.clear.all(I.vended(ledger.deps(P.ledger.next(w))), '\n') == True{} : Bool}
  for ne: {String.eq("ez.lock.toml", p) == False{} : Bool}
  for rb: ML.ReadsBack()
  {P.put(after(w), p) == P.Kept{} : P.Wrote}

# LAW: with no ez.toml, `ez lock` refuses, plain or `--upgrade`, whatever
# else the World holds, so with `lock_refusal_writes_nothing` it writes
# nothing
# EZ-LED-6
law lock_needs_ledger:
  for up: Bool
  for +only: String
  for here: String
  for listing: W.Listing
  for rs: List<&2, W.Reply>
  for us: List<&2, Up.Reply>
  {P.refuses(W.World{W.Args{up, only, here}, None{}, listing, rs, us}) == True{} : Bool}

# LAW: and a ledger that does not parse is refused the same way, so no lock
# is made from a guess
# EZ-LED-1
law lock_refuses_unread:
  for up: Bool
  for +only: String
  for here: String
  for +s: String
  for listing: W.Listing
  for rs: List<&2, W.Reply>
  for us: List<&2, Up.Reply>
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {P.refuses(W.World{W.Args{up, only, here}, Some{s}, listing, rs, us}) == True{} : Bool}

# LAW: every tree `ez lock` lays, plain or `--upgrade`, has the manifest of
# the texts it lays as its last file, each weighed by its own text, and is
# named by that manifest's `0x` hash. A package whose manifest hashes to its
# name but is not written the way the name is taken is refused, not laid.
# EZ-HASH-3
law lock_lays_named:
  for +w: W.World
  {P.lays.named(P.effects(P.plan(w))) == True{} : Bool}

# EZ-LED-8 for `ez lock` and `ez lock --upgrade`: a source is recorded as the
# ledger gives it, and every question git is asked about it names it anchored
# at the project, as the planner computes it. The directory the lock runs in,
# which is the project root, is `W.args.here`.

# the origins of the ledger the lock is made from: ez.toml's for a plain
# lock, the ledger the upgrade leaves for `--upgrade`
def origins(world: W.World) -> List<&2, L.Origin>:
  W.next.origins(up.next(world))

# the package questions a step asks, none when it runs its plan
def step.pkgs(st: P.Step) -> List<&2, W.Ask>:
  match st:
    case P.Asking{asks, _ups, _names}:
      asks
    case P.Run{_plan}:
      []

# the upgrade's queries a step asks, none when it runs its plan
def step.queries(st: P.Step) -> List<&2, P.Query>:
  match st:
    case P.Asking{_asks, ups, _names}:
      ups
    case P.Run{_plan}:
      []

# whether a package question names the source `orgs` records for its hash,
# anchored at `here`
def pkg.anchored(+here: String, +orgs: List<&2, L.Origin>, ask: W.Ask) -> Bool:
  match ask:
    case W.Pkg{+h, src, _hub}:
      String.eq(L.src.url(src), L.src.url(P.anchor.src(here, L.origin(orgs, h))))
    case _:
      True{}

# whether every package question does
def pkgs.anchored(+here: String, +orgs: List<&2, L.Origin>, as: List<&2, W.Ask>) -> Bool:
  match as:
    case []:
      True{}
    case h <> t:
      +rest = pkgs.anchored(here, orgs, t)
      Bool.and(pkg.anchored(here, orgs, h), rest)

# whether git is asked a query as the upgrade's question with its source
# anchored at `here`
def query.anchored(+here: String, query: P.Query) -> Bool:
  P.Query{ask, git} = query
  String.eq(Up.key(git), Up.key(Up.anchor(here, ask)))

# whether every query is
def queries.anchored(+here: String, qs: List<&2, P.Query>) -> Bool:
  match qs:
    case []:
      True{}
    case h <> t:
      +rest = queries.anchored(here, t)
      Bool.and(query.anchored(here, h), rest)

# the upgrade's questions a list of queries asks
def queries.asks(qs: List<&2, P.Query>) -> List<&2, Up.Ask>:
  match qs:
    case []:
      []
    case P.Query{ask, _git} <> t:
      ask <> queries.asks(t)

# LAW: every package question `ez lock` asks, plain or `--upgrade`, names the
# source the ledger it is made from records for that package, anchored at
# the project: a URL and an absolute path as they are, and a relative path
# joined to the project root
# EZ-LED-8
law lock_asks_anchored:
  for +w: W.World
  {pkgs.anchored(W.args.here(w), origins(w), step.pkgs(P.step(w))) == True{} : Bool}

# LAW: the upgrade's questions a step puts to git are exactly the questions
# the upgrade still has (`P.wants.up`), the ones EZ-RES-4 to 8 are stated
# over
# EZ-LED-8
law upgrade_asks_its_questions:
  for +w: W.World
  {queries.asks(step.queries(P.step(w))) == P.wants.up(w) : List<&2, Up.Ask>}

# LAW: and git is asked each with the source it names anchored at the
# project, while the upgrade looks the answer up by the source as the ledger
# records it
# EZ-LED-8
law upgrade_asks_anchored:
  for +w: W.World
  {queries.anchored(W.args.here(w), step.queries(P.step(w))) == True{} : Bool}

# LAW: every package `ez lock` resolves, plain or `--upgrade`, and so every
# package its lock renders, carries the source the ledger it is made from
# records for its hash, as that ledger gives it, never anchored
# EZ-LED-8
law lock_records_as_given:
  for +w: W.World
  {pinned.all(origins(w), P.packs(w)) == P.packs(w) : List<&2, L.Pack>}

# the source a dependency records
def dep.url(dep: M.Dep) -> String:
  M.source.url(M.source.dep(dep))

# the sources dependencies record, in order
def dep.urls(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case h <> t:
      dep.url(h) <> dep.urls(t)

# the source a tool pin records
def tool.url(pin: M.Tool) -> String:
  M.source.url(M.tool.source(pin))

# the sources tool pins record, in order
def tool.urls(ts: List<&2, M.Tool>) -> List<&2, String>:
  match ts:
    case []:
      []
    case h <> t:
      tool.url(h) <> tool.urls(t)

# the tool pins of a ledger model, none when it did not parse
def ledger.tools(read: M.Read) -> List<&2, M.Tool>:
  match read:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _hpa, _hpv, _ds, ts} = m
      ts

# whether a ledger parsed
def ledger.good(read: M.Read) -> Bool:
  match read:
    case M.Bad{_why}:
      False{}
    case M.Good{_m}:
      True{}

# LAW: the ledger model `ez lock --upgrade` renders into ez.toml records every
# dependency's source as ez.toml gave it: the same sources, in the same
# order, a relative path still relative to the project. A pin that moves is
# retargeted to a new commit of the same source. A plain lock renders
# ez.toml's model as it is.
# EZ-LED-8
law upgrade_records_as_given:
  for +w: W.World
  {dep.urls(ledger.deps(P.ledger.next(w))) == dep.urls(ledger.deps(W.parsed(W.ledger.of(w))))
    : List<&2, String>}

# LAW: and every tool pin's source the same way
# EZ-LED-8
law upgrade_records_tools_as_given:
  for +w: W.World
  {tool.urls(ledger.tools(P.ledger.next(w))) == tool.urls(ledger.tools(W.parsed(W.ledger.of(w))))
    : List<&2, String>}

# LAW: when `ez lock --upgrade` does not refuse and leaves `.gitignore`
# unwritten, it leaves it because it was in sync already: the file it read
# has the allowlist of exactly the hashes the upgrade commits, each once. No
# vendored hash holds a newline.
# EZ-VEN-1
law upgrade_allowlist_kept_in_sync:
  for +w: W.World
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for kept: {P.put(w, ".gitignore") == P.Kept{} : P.Wrote}
  for +ev: {Str.clear.all(vends(w), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(ignore.read(w))) == vends(w) : List<&2, String>}

# LAW: and when it leaves ez.toml unwritten, which it does when no pin
# moved, the hashes it commits are the vendored hashes of ez.toml as it is
# EZ-VEN-1
law upgrade_unmoved_vends_the_ledger:
  for +w: W.World
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +ok: {P.refuses(w) == False{} : Bool}
  for kept: {P.put(w, "ez.toml") == P.Kept{} : P.Wrote}
  {vends(w) == I.vended(ledger.deps(W.parsed(W.ledger.of(w)))) : List<&2, String>}

# LAW: the origins `ez lock` reads packages by are the dependencies of
# ez.toml alone: a `[tools.*]` pin is never an origin, whatever tools the
# ledger pins. `ez lock --upgrade` reads the ledger it leaves the same way
# (`W.next.origins`, through `L.ledger.read`).
# EZ-LED-5
law lock_origins_skip_tools:
  for +s: String
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for g: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(s) : M.Read}
  {W.origins(Some{s}) == L.ledger.origins(ds) : List<&2, L.Origin>}

# LAW: and so are the origins `ez lock --upgrade` reads packages by, over the
# ledger the upgrade leaves, whatever tools that ledger pins
# EZ-LED-5
law upgrade_origins_skip_tools:
  for +nx: Up.Next
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for g: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == Up.next.read(nx) : M.Read}
  {W.next.origins(nx) == L.ledger.origins(ds) : List<&2, L.Origin>}

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
    == W.git.body(List.is_empty(&2, K.File, K.bare(L.manifest.files(String.lines(manifest)))),
      hash, K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))),
      K.bare.srcs(L.manifest.files(String.lines(manifest)), ss)) : W.Verdict}

# LAW: and `ez lock --upgrade` weighs a pinned commit the same way: when the
# walk's hash is not the pin, the pin is compared with the checkout's hash
# without its LICENSE files, which is the pin exactly when it was taken so
law upgrade_named_without_license:
  for +pin: String
  for +manifest: String
  for walked: {False{} == String.eq(Up.hash.of(manifest), pin) : Bool}
  for bare: {True{} == String.eq(Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(
    String.lines(manifest))))), pin) : Bool}
  {Up.hash.kept(pin, manifest)
    == Up.hash.of(K.manifest.lines(K.bare(L.manifest.files(String.lines(manifest)))))
    : String}

# ---------------------------------------------------------------------------
# Named hub imports (EZ-HUB). A `<name>@<version>` import is a hub package:
# the lock reads it by its name, resolves the name by a table of names, walks
# the package the table gives it, and records the pair under `[names]`. The
# table is the names ez.toml records, each with the hash beside it, first,
# then those the answers resolve: the lock being rewritten's, then the hub's.
# A name is put to the hub only when nothing before it resolves it, and a
# lock that is made lays, for every name it records, the file bend reads the
# name's hash from.

# the names files a list of effects lays, in order. Law vocabulary.
def names.laid(es: List<&2, P.Effect>) -> List<&2, L.Name>:
  match es:
    case []:
      []
    case e <> t:
      match e:
        case P.Name{nv, hash}:
          L.Name{nv, hash} <> names.laid(t)
        case _:
          names.laid(t)

# whether every name of a list is recorded with the hash a table gives it.
# Law vocabulary.
def names.agree(+ns: List<&2, L.Name>, ps: List<&2, L.Name>) -> Bool:
  match ps:
    case []:
      True{}
    case L.Name{+n, h} <> t:
      +rest = names.agree(ns, t)
      Bool.and(String.eq(L.name.find(ns, n), h), rest)

# whether a question puts this name to the hub. Law vocabulary.
def ask.named(ask: W.Ask, +nv: String) -> Bool:
  match ask:
    case W.Name{n, _hub}:
      String.eq(n, nv)
    case _:
      False{}

# whether a list of questions puts this name to the hub. Law vocabulary.
def asks.name(as: List<&2, W.Ask>, +nv: String) -> Bool:
  match as:
    case []:
      False{}
    case h <> t:
      L.any.step(ask.named(h, nv), _u => asks.name(t, nv))

# the table of names the lock resolves names by on a World, as its questions
# are asked: ez.toml's names first, then those the answers resolve. Law
# vocabulary.
def names.table(world: W.World) -> List<&2, L.Name>:
  W.World{+args, +ledger, _listing, replies, +ups} = world
  P.table(Up.next.read(W.next(args, ledger, ups)),
    P.scan(W.replies.of(W.next(args, ledger, ups), replies)))

# LAW: the lock reads a named import as the package its name names, never as
# a module of the project, whether or not the hub rules the name in
# EZ-HUB-3
law lock_reads_named:
  for +spec: String
  for e: {False{} == String.is_empty(K.named.of(spec)) : Bool}
  {L.named.put(spec) == [K.named.of(spec)] : List<&2, String>}

# LAW: a package's named import queues the package the table gives its name,
# so the walk reaches, and checks against its manifest, the hash the name
# resolves to
# EZ-HUB-1
law named_kid_queued:
  for +ns: List<&2, L.Name>
  for +nvs: List<&2, String>
  for +nv: String
  for e: {L.seen.holds(nvs, nv) == True{} : Bool}
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  {L.seen.holds(L.name.hashes(ns, nvs), L.name.find(ns, nv)) == True{} : Bool}

# LAW: and every name the lock records, it records with the hash the table
# gives it, the same hash
# EZ-HUB-1
law lock_names_agree:
  for +ns: List<&2, L.Name>
  for nvs: List<&2, String>
  {names.agree(ns, L.name.pairs(ns, nvs)) == True{} : Bool}

# LAW: a name ez.toml records resolves to the hash ez.toml records beside
# it, whatever the answers say
# EZ-HUB-1
law ledger_names_first:
  for +led: M.Read
  for +js: List<&2, W.Judged>
  for +nv: String
  for f: {False{} == String.is_empty(L.name.find(L.ledger.names(led), nv)) : Bool}
  {L.name.find(P.table(led, js), nv) == L.name.find(L.ledger.names(led), nv) : String}

# LAW: the lock being rewritten, read, resolves every name it records that
# bend would read back, so those names join the table without the hub
# EZ-HUB-2
law lock_answer_names:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +key: String
  for text: String
  {W.accept(orgs, hub, key, W.Locked{text}) == W.Named{L.names.read(text)} : W.Verdict}

# LAW: a name the table resolves, because ez.toml records it or the lock
# being rewritten does, is never put to the hub
# EZ-HUB-2
law resolved_not_asked:
  for +w: W.World
  for +nv: String
  for r: {False{} == String.is_empty(L.name.find(names.table(w), nv)) : Bool}
  {asks.name(P.wants.names(w), nv) == False{} : Bool}

# LAW: a lock that is made lays a names file for every name the lock it
# writes records, with the hash it records, and none other
# EZ-HUB-4
law lock_lays_its_names:
  for +w: W.World
  for +t: String
  for d: {P.Doc{t} == P.decide(W.inputs(w)) : P.Doc}
  {names.laid(P.effects(P.plan(w))) == L.names.read(t) : List<&2, L.Name>}
