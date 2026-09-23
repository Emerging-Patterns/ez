# lock: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import ./up.bend as Up
import ../manifest/upgrade.bend as U
import ../manifest/manifest.bend as M
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../pkg/pkg.bend as K
import ../pkg/LAWS.bend as KL
import ../pkg/PROOF.bend as KP
import ./LAWS.bend as Laws

def Laws.origin_first(h, s, rest):
  Equal.cong(Bool, L.Src, b => Bool.pick(L.Src, b, s, L.origin(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

# The head's hash compared with itself is the arm that answers at once.
def Laws.known_first(h, _s, rest):
  Equal.cong(Bool, Bool, b => L.any.step(b, _u => L.known(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

# A NAR hash that is not empty takes the second arm, and one compared with
# itself is the arm that passes.
def Laws.nar_why_agrees(n, url, rev, f):
  %f : {L.nar.why.go(_, String.eq(n, n), n, n, url, rev) == "" : String}
  Equal.cong(Bool, String, b => L.nar.why.go(False{}, b, n, n, url, rev),
    String.eq(n, n), True{}, Eq.string_eq_self(n))

# Both tests are rewritten to the False the premises give, and the reason
# that is left opens with a literal, so it is not empty.
def Laws.nar_why_refuses(want, got, url, rev, f, d):
  %f : {String.is_empty(L.nar.why.go(_, String.eq(want, got), want, got, url,
    rev)) == False{} : Bool}
  %d : {String.is_empty(L.nar.why.go(False{}, _, want, got, url, rev))
    == False{} : Bool}
  {==}

def Laws.nar_why_needs_a_hash(_got, _url, _rev):
  {==}

# Insertion rewrites its comparison into the arm that writes the
# package first. The hub name and the two closed document laws reduce.
# `spec_hash` is the first piece of a split walked one character at a
# time.

def Laws.pack_ins_le(x, h, t, e):
  %e : {L.pack.ins.put(_, x, h, t, L.pack.ins(t, x))
    == x <> (h <> t) : List<&2, L.Pack>}
  {==}

def Laws.lock_names_hub(_hub, _ps):
  {==}

def Laws.render_keeps_packages_without_tools(_hub, _ps):
  {==}

# The order a lock is written in. The lock's text depends on its packages
# only through their blocks sorted by `K.file.sort`. A package list
# rearranged is its blocks rearranged the same way, and distinct hashes are
# distinct block paths, so pkg's `sort_perm` sorts either list's blocks into
# the same list.

# LAW: a package put at a place is its block put at the same place
law blocks_ins_at:
  for +n: Nat
  for +x: L.Pack
  for +ps: List<&2, L.Pack>
  {L.pack.blocks(Laws.perm.ins_at(n, x, ps))
    == KL.perm.ins_at(n, L.pack.block(x), L.pack.blocks(ps)) : List<&2, K.File>}

def blocks_ins_at(n, x, ps):
  match n ps:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      Equal.cong(List<&2, K.File>, List<&2, K.File>,
        bs => L.pack.block(h) <> bs,
        L.pack.blocks(Laws.perm.ins_at(p, x, t)),
        KL.perm.ins_at(p, L.pack.block(x), L.pack.blocks(t)),
        blocks_ins_at(p, x, t))

# LAW: a package list rearranged is its blocks rearranged
law blocks_perm:
  for +ns: List<&2, Nat>
  for +ps: List<&2, L.Pack>
  {L.pack.blocks(Laws.perm(ns, ps)) == KL.perm(ns, L.pack.blocks(ps))
    : List<&2, K.File>}

def blocks_perm(ns, ps):
  match ns ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{h, t}:
      {==}
    case Con{n, ms} Nil{}:
      {==}
    case Con{+n, +ms} Con{+h, +t}:
      Equal.trans(List<&2, K.File>,
        L.pack.blocks(Laws.perm.ins_at(n, h, Laws.perm(ms, t))),
        KL.perm.ins_at(n, L.pack.block(h), L.pack.blocks(Laws.perm(ms, t))),
        KL.perm.ins_at(n, L.pack.block(h), KL.perm(ms, L.pack.blocks(t))),
        blocks_ins_at(n, h, Laws.perm(ms, t)),
        Equal.cong(List<&2, K.File>, List<&2, K.File>,
          bs => KL.perm.ins_at(n, L.pack.block(h), bs),
          L.pack.blocks(Laws.perm(ms, t)), KL.perm(ms, L.pack.blocks(t)),
          blocks_perm(ms, t)))

# LAW: a hash no package of a list has is a path no block of it has, whatever
# the block's text
law fresh_blocks:
  for +x: String
  for +s: String
  for +ps: List<&2, L.Pack>
  {Laws.hash.fresh(x, ps) == KL.fresh(K.File{x, s}, L.pack.blocks(ps)) : Bool}

def fresh_blocks(x, s, ps):
  match ps:
    case []:
      {==}
    case L.Pack{+h, _src, _fs} <> +t:
      Equal.cong(Bool, Bool, b => Bool.and(Bool.not(String.eq(x, h)), b),
        Laws.hash.fresh(x, t), KL.fresh(K.File{x, s}, L.pack.blocks(t)),
        fresh_blocks(x, s, t))

# LAW: so distinct hashes are distinct block paths
law distinct_blocks:
  for +ps: List<&2, L.Pack>
  {Laws.distinct(ps) == KL.distinct(L.pack.blocks(ps)) : Bool}

def distinct_blocks(ps):
  match ps:
    case []:
      {==}
    case L.Pack{+h, +src, +fs} <> +t:
      Equal.trans(Bool,
        Bool.and(Laws.hash.fresh(h, t), Laws.distinct(t)),
        Bool.and(KL.fresh(L.pack.block(L.Pack{h, src, fs}), L.pack.blocks(t)),
          Laws.distinct(t)),
        Bool.and(KL.fresh(L.pack.block(L.Pack{h, src, fs}), L.pack.blocks(t)),
          KL.distinct(L.pack.blocks(t))),
        Equal.cong(Bool, Bool, b => Bool.and(b, Laws.distinct(t)),
          Laws.hash.fresh(h, t),
          KL.fresh(L.pack.block(L.Pack{h, src, fs}), L.pack.blocks(t)),
          fresh_blocks(h, T.render(L.pack.sects.of(h, src, K.files_of(fs))), t)),
        Equal.cong(Bool, Bool,
          b => Bool.and(KL.fresh(L.pack.block(L.Pack{h, src, fs}),
            L.pack.blocks(t)), b),
          Laws.distinct(t), KL.distinct(L.pack.blocks(t)), distinct_blocks(t)))

# LAW: the blocks of a rearranged list of distinct hashes sort to the blocks
# of the list, sorted
law blocks_sort_perm:
  for +ns: List<&2, Nat>
  for +ps: List<&2, L.Pack>
  for dis: {Laws.distinct(ps) == True{} : Bool}
  {K.file.sort(L.pack.blocks(Laws.perm(ns, ps))) == K.file.sort(L.pack.blocks(ps))
    : List<&2, K.File>}

def blocks_sort_perm(ns, ps, dis):
  Equal.trans(List<&2, K.File>,
    K.file.sort(L.pack.blocks(Laws.perm(ns, ps))),
    K.file.sort(KL.perm(ns, L.pack.blocks(ps))),
    K.file.sort(L.pack.blocks(ps)),
    Equal.cong(List<&2, K.File>, List<&2, K.File>, bs => K.file.sort(bs),
      L.pack.blocks(Laws.perm(ns, ps)), KL.perm(ns, L.pack.blocks(ps)),
      blocks_perm(ns, ps)),
    KL.sort_perm(ns, L.pack.blocks(ps),
      Equal.trans(Bool, KL.distinct(L.pack.blocks(ps)), Laws.distinct(ps), True{},
        Equal.sym(Bool, Laws.distinct(ps), KL.distinct(L.pack.blocks(ps)),
          distinct_blocks(ps)),
        dis)))

# The text is the sorted blocks under the `[lock]` table and before the
# tools, so it follows.
def Laws.lock_order_free(ns, ps, ts, hub, dis):
  Equal.cong(List<&2, K.File>, String,
    bs => L.text.of(hub, bs, T.render.all(L.tool.sects(ts))),
    K.file.sort(L.pack.blocks(Laws.perm(ns, ps))), K.file.sort(L.pack.blocks(ps)),
    blocks_sort_perm(ns, ps, dis))

# A block renders its files sorted, so this is `sort_perm` under the block.
def Laws.pack_order_free(ns, hash, src, fs, dis):
  Equal.cong(List<&2, K.File>, K.File,
    ys => K.File{hash, T.render(L.pack.sects.of(hash, src, K.dedup(ys)))},
    K.file.sort(KL.perm(ns, fs)), K.file.sort(fs), KL.sort_perm(ns, fs, dis))

# LAW: one character before the slash, with the separator test given as
# a parameter, since a match may not scrutinise a computed value
law spec_split.step:
  for +h: Char
  for +t: String
  for +r: String
  for e: {False{} == Char.is_eq(h, '/') : Bool}
  for ih: {String.split(String.append(t, SCon{'/', r}), '/')
    == t <> String.split(r, '/') : List<&2, String>}
  {String.split(String.append(SCon{h, t}, SCon{'/', r}), '/')
    == SCon{h, t} <> String.split(r, '/') : List<&2, String>}

def spec_split.step(h, t, r, e, ih):
  %e : {String.split.fin(h, String.split(String.append(t, SCon{'/', r}), '/'), _)
    == SCon{h, t} <> String.split(r, '/') : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>,
    x => String.split.fin(h, x, False{}),
    String.split(String.append(t, SCon{'/', r}), '/'),
    t <> String.split(r, '/'), ih)

# LAW: a spec that holds `/` first at a known place splits there
law spec_split:
  for +s: String
  for +r: String
  for +e: {Laws.slashless(s) == True{} : Bool}
  {String.split(String.append(s, SCon{'/', r}), '/')
    == s <> String.split(r, '/') : List<&2, String>}

def spec_split(s, r, e):
  match s:
    case SNil{}:
      Equal.cong(Bool, List<&2, String>,
        x => String.split.fin('/', String.split(r, '/'), x),
        Char.is_eq('/', '/'), True{}, Eq.char_eq_self('/'))
    case SCon{+h, +t}:
      spec_split.step(h, t, r,
        Equal.sym(Bool, Char.is_eq(h, '/'), False{},
          Eq.not.true(Char.is_eq(h, '/'),
            Eq.and.left(Bool.not(Char.is_eq(h, '/')), Laws.slashless(t), e))),
        spec_split(t, r,
          Eq.and.right(Bool.not(Char.is_eq(h, '/')), Laws.slashless(t), e)))

def Laws.spec_hash(h, rest, e):
  Equal.cong(List<&2, String>, String,
    ws => K.word(ws, 0n),
    String.split(String.append(h, SCon{'/', rest}), '/'),
    h <> String.split(rest, '/'),
    spec_split(h, rest, e))

# The planner. A made plan's effects are the lines a person is told, the
# checked trees laid, the upgrade's files, the committed trees removed, and the
# lock written last. A line, a lay and a removal write no path, and the lock's
# write comes after every other, so what the plan leaves at the lock's path is
# what the planner decided, plain or upgrade.

# LAW: one tree laid, or passed over, leaves every path as it was
law pick_put:
  for b: Bool
  for v: W.Verdict
  for pl: P.Place
  for +h: String
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.lay.pick(b, v, pl, h, rest), p) == P.put.in(rest, p) : P.Wrote}

def pick_put(b, v, _pl, _h, _rest, _p):
  match b:
    case True{}:
      match v:
        case W.No{_why}:
          {==}
        case W.Ok{fs, ss}:
          {==}
    case False{}:
      {==}

# LAW: and so do all of them, wherever each is laid
law lays_put:
  for +cs: List<&2, String>
  for +vs: List<&2, String>
  for js: List<&2, W.Judged>
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.lays(cs, vs, js, rest), p) == P.put.in(rest, p) : P.Wrote}

def lays_put(cs, vs, js, rest, p):
  match js:
    case []:
      {==}
    case W.Judged{+h, +v} <> +t:
      Equal.trans(P.Wrote,
        P.put.in(P.lay.pick(L.seen.holds(cs, h), v, P.place.of(L.seen.holds(vs, h)),
          h, P.lays(cs, vs, t, rest)), p),
        P.put.in(P.lays(cs, vs, t, rest), p),
        P.put.in(rest, p),
        pick_put(L.seen.holds(cs, h), v, P.place.of(L.seen.holds(vs, h)), h,
          P.lays(cs, vs, t, rest), p),
        lays_put(cs, vs, t, rest, p))

# LAW: a line a person is told leaves every path as it was
law says_put:
  for ss: List<&2, String>
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.says.of(ss, rest), p) == P.put.in(rest, p) : P.Wrote}

def says_put(ss, rest, p):
  match ss:
    case []:
      {==}
    case _h <> t:
      says_put(t, rest, p)

# LAW: and so does a committed tree removed
law drops_put:
  for ds: List<&2, String>
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.drops.of(ds, rest), p) == P.put.in(rest, p) : P.Wrote}

def drops_put(ds, rest, p):
  match ds:
    case []:
      {==}
    case _h <> t:
      drops_put(t, rest, p)

# LAW: the upgrade's files are written before what follows them, so a path
# whose last write follows them is left holding that write
law edits_last:
  for es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  for +p: String
  for +t: String
  for e: {P.put.in(rest, p) == P.Put{t} : P.Wrote}
  {P.put.in(P.edits.of(es, rest), p) == P.Put{t} : P.Wrote}

def edits_last(es, rest, p, t, e):
  match es:
    case []:
      e
    case Up.Edit{at, text} <> tl:
      Equal.cong(P.Wrote, P.Wrote, x => P.put.one(P.Write{at, text}, p, x),
        P.put.in(P.edits.of(tl, rest), p), P.Put{t}, edits_last(tl, rest, p, t, e))

# LAW: what a plan leaves at the lock's path is what the planner decided,
# whatever the upgrade wrote around it
law made_put:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  {P.put.plan(P.made(nx, cs, js, d), "ez.lock.toml") == Laws.put.doc(d) : P.Wrote}

def made_put(nx, cs, js, d):
  match d:
    case P.Doc{+text}:
      Equal.trans(P.Wrote,
        P.put.in(P.says.of(Up.next.says(nx),
          P.lays(cs, Up.next.vends(nx), js,
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))))),
          "ez.lock.toml"),
        P.put.in(P.lays(cs, Up.next.vends(nx), js,
          P.edits.of(Up.next.edits(nx),
            P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}])))),
          "ez.lock.toml"),
        P.Put{text},
        says_put(Up.next.says(nx),
          P.lays(cs, Up.next.vends(nx), js,
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}])))),
          "ez.lock.toml"),
        Equal.trans(P.Wrote,
          P.put.in(P.lays(cs, Up.next.vends(nx), js,
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}])))),
            "ez.lock.toml"),
          P.put.in(P.edits.of(Up.next.edits(nx),
            P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))),
            "ez.lock.toml"),
          P.Put{text},
          lays_put(cs, Up.next.vends(nx), js,
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))),
            "ez.lock.toml"),
          edits_last(Up.next.edits(nx),
            P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}])),
            "ez.lock.toml", text,
            edits_last(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]),
              "ez.lock.toml", text,
              drops_put(Up.next.drops(nx), [P.Write{P.lockfile(), text}],
                "ez.lock.toml")))))
    case P.Stop{_why}:
      {==}

# LAW: and a plain lock leaves nothing at ez.toml, whatever was decided
law made_keeps_ledger:
  for +led: M.Read
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  {P.put.plan(P.made(Up.plain(led), cs, js, d), "ez.toml") == P.Kept{} : P.Wrote}

def made_keeps_ledger(_led, cs, js, d):
  match d:
    case P.Doc{text}:
      lays_put(cs, [], js, [P.Write{P.lockfile(), text}], "ez.toml")
    case P.Stop{_why}:
      {==}

# LAW: what `ez lock` writes to its lock is a function of what the planner
# decided over the World's Inputs
law put_decides:
  for w: W.World
  {P.put(w, "ez.lock.toml") == Laws.put.doc(P.decide(W.inputs(w))) : P.Wrote}

def put_decides(w):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      made_put(W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}))

def Laws.lock_reproducible(w1, w2, e):
  Equal.trans(P.Wrote,
    P.put(w1, "ez.lock.toml"),
    Laws.put.doc(P.decide(W.inputs(w1))),
    P.put(w2, "ez.lock.toml"),
    put_decides(w1),
    Equal.trans(P.Wrote,
      Laws.put.doc(P.decide(W.inputs(w1))),
      Laws.put.doc(P.decide(W.inputs(w2))),
      P.put(w2, "ez.lock.toml"),
      Equal.cong(W.Inputs, P.Wrote, ins => Laws.put.doc(P.decide(ins)),
        W.inputs(w1), W.inputs(w2), e),
      Equal.sym(P.Wrote, P.put(w2, "ez.lock.toml"),
        Laws.put.doc(P.decide(W.inputs(w2))), put_decides(w2))))

# LAW: a source of either kind judges a BEND_LIB tree as a clone weighed to
# the narHash it records
law lib_as_clone.src:
  for src: L.Src
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(src, W.Lib{}, hash, manifest, ss)
    == W.accept.src(src, W.Clone{L.src.nar(src)}, hash, manifest, ss)
    : W.Verdict}

def lib_as_clone.src(src, _hash, _manifest, _ss):
  match src:
    case L.Hub{}:
      {==}
    case L.Git{url, rev, entry, root, nar, tag}:
      {==}

def Laws.lib_judged_as_clone(orgs, _hub, hash, manifest, ss):
  lib_as_clone.src(L.origin(orgs, hash), hash, manifest, ss)

# LAW: how the bytes arrived, as a fresh clone would have it, is judged as it
# was, for a source of either kind
law reclone.how_judged:
  for src: L.Src
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(src, W.reclone.how(how, src), hash, manifest, ss)
    == W.accept.src(src, how, hash, manifest, ss) : W.Verdict}

def reclone.how_judged(src, how, hash, manifest, ss):
  match how:
    case W.Lib{}:
      Equal.sym(W.Verdict,
        W.accept.src(src, W.Lib{}, hash, manifest, ss),
        W.accept.src(src, W.Clone{L.src.nar(src)}, hash, manifest, ss),
        lib_as_clone.src(src, hash, manifest, ss))
    case W.Clone{got}:
      {==}
    case W.Served{}:
      {==}

# LAW: one answer, as a fresh clone would have it, is judged as it was
law reclone.one_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {W.accept(orgs, hub, hash, W.reclone.one(orgs, hash, a))
    == W.accept(orgs, hub, hash, a) : W.Verdict}

def reclone.one_judged(orgs, _hub, hash, a):
  match a:
    case W.Miss{why}:
      {==}
    case W.Got{how, manifest, ss}:
      reclone.how_judged(L.origin(orgs, hash), how, hash, manifest, ss)

# LAW: every answer, as a fresh clone would have it, is judged as it was
law reclone_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {W.judge(orgs, hub, W.reclone.all(orgs, rs)) == W.judge(orgs, hub, rs)
    : List<&2, W.Judged>}

def reclone_judged(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+ask, a} <> t:
      Equal.trans(List<&2, W.Judged>,
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask),
          W.reclone.one(orgs, W.ask.hash(ask), a))}
          <> W.judge(orgs, hub, W.reclone.all(orgs, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, W.reclone.all(orgs, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, t),
        Equal.cong(W.Verdict, List<&2, W.Judged>,
          v => W.Judged{W.ask.hash(ask), v} <> W.judge(orgs, hub, W.reclone.all(orgs, t)),
          W.accept(orgs, hub, W.ask.hash(ask), W.reclone.one(orgs, W.ask.hash(ask), a)),
          W.accept(orgs, hub, W.ask.hash(ask), a),
          reclone.one_judged(orgs, hub, W.ask.hash(ask), a)),
        Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
          js => W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)} <> js,
          W.judge(orgs, hub, W.reclone.all(orgs, t)),
          W.judge(orgs, hub, t),
          reclone_judged(orgs, hub, t)))

# LAW: a fresh clone's World has the Inputs of the World it was made from
law reclone_inputs:
  for w: W.World
  {W.inputs(W.reclone(w)) == W.inputs(w) : W.Inputs}

def reclone_inputs(w):
  match w:
    case W.World{+args, +ledger, listing, replies, +ups}:
      Equal.cong(List<&2, W.Judged>, W.Inputs,
        js => W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          List.append(&2, W.Judged,
            W.judge(W.next.origins(W.next(args, ledger, ups)),
              W.next.hub(W.next(args, ledger, ups)),
              W.laid.replies(Up.next.trees(W.next(args, ledger, ups)),
                W.next.origins(W.next(args, ledger, ups)),
                W.next.hub(W.next(args, ledger, ups)))), js)},
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)),
          W.reclone.all(W.next.origins(W.next(args, ledger, ups)), replies)),
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies),
        reclone_judged(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies))

def Laws.clone_reproduces(w):
  Laws.lock_reproducible(W.reclone(w), w, reclone_inputs(w))

# A plain lock's World is one whose args say no `--upgrade`; the other arm
# contradicts the premise.
def Laws.plain_lock_keeps_ledger(w, e):
  match w:
    case W.World{args, +ledger, listing, +replies, ups}:
      match args:
        case W.Args{up, only}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.put(W.World{W.Args{True{}, only}, ledger, listing,
                replies, ups}, "ez.toml") == P.Kept{} : P.Wrote}, e)
            case False{}:
              made_keeps_ledger(W.parsed(ledger),
                P.cloned(W.replies.of(Up.plain(W.parsed(ledger)), replies)),
                W.judged.of(Up.plain(W.parsed(ledger)), replies),
                P.decide(W.Inputs{W.parsed(ledger), "", listing,
                  W.judged.of(Up.plain(W.parsed(ledger)), replies)}))

# LAW: a plan made from a refusal has no effect that writes, whatever the
# upgrade decided around it
law made_refused:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for r: {P.refuses.doc(d) == True{} : Bool}
  {P.writes(P.made(nx, cs, js, d)) == False{} : Bool}

def made_refused(nx, cs, js, d, r):
  match d:
    case P.Doc{text}:
      Eq.bit.absurd(&2, {P.writes(P.made(nx, cs, js, P.Doc{text})) == False{} : Bool}, r)
    case P.Stop{_why}:
      {==}

def Laws.lock_refusal_writes_nothing(w, r):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      made_refused(W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}), r)

# A plain World's args say no `--upgrade`; the other arm contradicts the
# premise, and in this one the upgrade is `Up.plain`, which asks nothing.
def Laws.plain_lock_asks_no_upgrade(w, e):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, only}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.wants.up(W.World{W.Args{True{}, only}, ledger,
                listing, replies, ups}) == [] : List<&2, Up.Ask>}, e)
            case False{}:
              {==}

def Laws.plain_lock_ledger_next(w, e):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, only}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.ledger.next(W.World{W.Args{True{}, only}, ledger,
                listing, replies, ups}) == W.parsed(ledger) : M.Read}, e)
            case False{}:
              {==}

# The walk's sources, one step at a time. Each lemma is one def of the step,
# with the value it branches on given as a parameter.

# LAW: a package resolved by its verdict carries the ledger's source
law verdict_pins:
  for v: W.Verdict
  for +orgs: List<&2, L.Origin>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {Laws.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.step.verdict(v, L.origin(orgs, hash),
    hash, rest, packs, asks, bad)))
    == P.walk.packs(P.step.verdict(v, L.origin(orgs, hash), hash, rest, packs,
      asks, bad)) : List<&2, L.Pack>}

def verdict_pins(v, orgs, hash, _rest, packs, _asks, _bad, e):
  match v:
    case W.No{_why}:
      e
    case W.Ok{fs, _ss}:
      Equal.cong(List<&2, L.Pack>, List<&2, L.Pack>,
        ps => L.Pack{hash, L.origin(orgs, hash), fs} <> ps,
        Laws.pinned.all(orgs, packs), packs, e)

# LAW: and one looked up, whether it was answered or not
law look_pins:
  for found: P.Look
  for +orgs: List<&2, L.Origin>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {Laws.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.step.look(found, L.origin(orgs, hash),
    hash, rest, packs, asks, bad)))
    == P.walk.packs(P.step.look(found, L.origin(orgs, hash), hash, rest, packs,
      asks, bad)) : List<&2, L.Pack>}

def look_pins(found, orgs, hash, rest, packs, asks, bad, e):
  match found:
    case P.Absent{}:
      e
    case P.Found{v}:
      verdict_pins(v, orgs, hash, rest, packs, asks, bad, e)

# LAW: and one passed over, or picked
law pick_pins:
  for seen: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {Laws.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.step.pick(seen, orgs, js, hash, rest,
    packs, asks, bad)))
    == P.walk.packs(P.step.pick(seen, orgs, js, hash, rest, packs, asks, bad))
    : List<&2, L.Pack>}

def pick_pins(seen, orgs, js, hash, rest, packs, asks, bad, e):
  match seen:
    case True{}:
      e
    case False{}:
      look_pins(P.look(js, hash), orgs, hash, rest, packs, asks, bad, e)

# LAW: and one step of the walk, whatever the queue held
law pop_pins:
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for queue: List<&2, String>
  for +packs: List<&2, L.Pack>
  for +asks: List<&2, String>
  for bad: String
  for e: {Laws.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.step.pop(orgs, js, queue, packs, asks,
    bad)))
    == P.walk.packs(P.step.pop(orgs, js, queue, packs, asks, bad))
    : List<&2, L.Pack>}

def pop_pins(orgs, js, queue, packs, asks, bad, e):
  match queue:
    case []:
      e
    case +h <> t:
      pick_pins(Bool.or(L.has(packs, h), L.seen.holds(asks, h)), orgs, js, h, t,
        packs, asks, bad, e)

# LAW: one step keeps every resolved package on the ledger's source
law step_pins:
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for wk: P.Walk
  for e: {Laws.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.walk.step(orgs, js, wk)))
    == P.walk.packs(P.walk.step(orgs, js, wk)) : List<&2, L.Pack>}

def step_pins(orgs, js, wk, e):
  match wk:
    case P.Walk{queue, packs, asks, bad}:
      pop_pins(orgs, js, queue, packs, asks, bad, e)

# LAW: a walk that ran out of fuel keeps the packages it had
law out_pins:
  for done: Bool
  for +orgs: List<&2, L.Origin>
  for wk: P.Walk
  for e: {Laws.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.walk.out(done, wk)))
    == P.walk.packs(P.walk.out(done, wk)) : List<&2, L.Pack>}

def out_pins(done, _orgs, wk, e):
  match done:
    case True{}:
      e
    case False{}:
      match wk:
        case P.Walk{_queue, _packs, _asks, _bad}:
          e

# LAW: a walk that is done is what it was, and one that is not goes on
law more_pins:
  for done: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for f: Nat
  for +wk: P.Walk
  for e: {Laws.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  for ih: {Laws.pinned.all(orgs, P.walk.packs(P.walk(f, orgs, js,
    P.walk.step(orgs, js, wk))))
    == P.walk.packs(P.walk(f, orgs, js, P.walk.step(orgs, js, wk)))
    : List<&2, L.Pack>}
  {Laws.pinned.all(orgs, P.walk.packs(P.walk.more(done, wk,
    now => P.walk(f, orgs, js, P.walk.step(orgs, js, now)))))
    == P.walk.packs(P.walk.more(done, wk,
      now => P.walk(f, orgs, js, P.walk.step(orgs, js, now)))) : List<&2, L.Pack>}

def more_pins(done, _orgs, _js, _f, _wk, e, ih):
  match done:
    case True{}:
      e
    case False{}:
      ih

def Laws.walk_pins_ledger_sources(fuel, orgs, js, wk, e):
  match fuel:
    case 0n:
      out_pins(P.walk.done(wk), orgs, wk, e)
    case 1n+f:
      more_pins(P.walk.done(wk), orgs, js, f, wk, e,
        Laws.walk_pins_ledger_sources(f, orgs, js, P.walk.step(orgs, js, wk),
          step_pins(orgs, js, wk, e)))

def Laws.plain_lock_pins_ledger_sources(w, e):
  match w:
    case W.World{args, +ledger, listing, +replies, ups}:
      match args:
        case W.Args{up, only}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {Laws.pinned.all(W.origins(ledger),
                P.packs(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}))
                == P.packs(W.World{W.Args{True{}, only}, ledger, listing, replies, ups})
                : List<&2, L.Pack>}, e)
            case False{}:
              match listing:
                case W.Unlisted{why}:
                  {==}
                case W.Listed{fs}:
                  Laws.walk_pins_ledger_sources(U32.to_nat(100000),
                    L.ledger.read(W.parsed(ledger)),
                    W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
                    P.Walk{P.roots(fs), [], [], ""}, {==})

# The walk's hashes, one step at a time, in the shape of its sources above. A
# step resolves a hash only in the arm where `L.has` answered False, so the
# facts it needs are what an `or`, an `any.step` and an `and` that answered
# are made of.

# LAW: the left half of an `or` that answered False
law or_left:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_left(a, _b, e):
  match a:
    case False{}:
      {==}
    case True{}:
      e

# LAW: the head of a scan that answered False
law any_head:
  for c: Bool
  for r: Unit -> Bool
  for e: {L.any.step(c, r) == False{} : Bool}
  {c == False{} : Bool}

def any_head(c, _r, e):
  match c:
    case False{}:
      {==}
    case True{}:
      e

# LAW: and the rest of it
law any_rest:
  for c: Bool
  for r: Unit -> Bool
  for e: {L.any.step(c, r) == False{} : Bool}
  {r(Unit{}) == False{} : Bool}

def any_rest(c, r, e):
  match c:
    case False{}:
      e
    case True{}:
      Eq.bit.absurd2(&2, {r(Unit{}) == False{} : Bool}, e)

# LAW: an `and` of two halves that answered True
law and_true:
  for u: Bool
  for v: Bool
  for eu: {u == True{} : Bool}
  for ev: {v == True{} : Bool}
  {Bool.and(u, v) == True{} : Bool}

def and_true(u, _v, eu, ev):
  match u:
    case True{}:
      ev
    case False{}:
      eu

# LAW: the negation of a bit that answered False
law not_false:
  for u: Bool
  for e: {u == False{} : Bool}
  {Bool.not(u) == True{} : Bool}

def not_false(u, e):
  match u:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, e)

# LAW: a hash a package list does not have is fresh to it
law has_fresh:
  for +ps: List<&2, L.Pack>
  for +x: String
  for +e: {L.has(ps, x) == False{} : Bool}
  {Laws.hash.fresh(x, ps) == True{} : Bool}

def has_fresh(ps, x, e):
  match ps:
    case []:
      {==}
    case +p <> +t:
      and_true(Bool.not(String.eq(x, L.pack.hash(p))), Laws.hash.fresh(x, t),
        not_false(String.eq(x, L.pack.hash(p)),
          any_head(String.eq(x, L.pack.hash(p)), _u => L.has(t, x), e)),
        has_fresh(t, x,
          any_rest(String.eq(x, L.pack.hash(p)), _u => L.has(t, x), e)))

# LAW: a package resolved by its verdict is one the walk did not have
law verdict_distinct:
  for v: W.Verdict
  for src: L.Src
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {Laws.distinct(packs) == True{} : Bool}
  for n: {L.has(packs, hash) == False{} : Bool}
  {Laws.distinct(P.walk.packs(P.step.verdict(v, src, hash, rest, packs, asks,
    bad))) == True{} : Bool}

def verdict_distinct(v, _src, hash, _rest, packs, _asks, _bad, e, n):
  match v:
    case W.No{_why}:
      e
    case W.Ok{_fs, _ss}:
      and_true(Laws.hash.fresh(hash, packs), Laws.distinct(packs),
        has_fresh(packs, hash, n), e)

# LAW: and one looked up, whether it was answered or not
law look_distinct:
  for found: P.Look
  for src: L.Src
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {Laws.distinct(packs) == True{} : Bool}
  for n: {L.has(packs, hash) == False{} : Bool}
  {Laws.distinct(P.walk.packs(P.step.look(found, src, hash, rest, packs, asks,
    bad))) == True{} : Bool}

def look_distinct(found, src, hash, rest, packs, asks, bad, e, n):
  match found:
    case P.Absent{}:
      e
    case P.Found{v}:
      verdict_distinct(v, src, hash, rest, packs, asks, bad, e, n)

# LAW: and one passed over, or picked because the walk did not have it
law pick_distinct:
  for seen: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for +asks: List<&2, String>
  for bad: String
  for e: {Laws.distinct(packs) == True{} : Bool}
  for hs: {Bool.or(L.has(packs, hash), L.seen.holds(asks, hash)) == seen : Bool}
  {Laws.distinct(P.walk.packs(P.step.pick(seen, orgs, js, hash, rest, packs,
    asks, bad))) == True{} : Bool}

def pick_distinct(seen, orgs, js, hash, rest, packs, asks, bad, e, hs):
  match seen:
    case True{}:
      e
    case False{}:
      look_distinct(P.look(js, hash), L.origin(orgs, hash), hash, rest, packs,
        asks, bad, e,
        or_left(L.has(packs, hash), L.seen.holds(asks, hash), hs))

# LAW: and one step of the walk, whatever the queue held
law pop_distinct:
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for queue: List<&2, String>
  for +packs: List<&2, L.Pack>
  for +asks: List<&2, String>
  for bad: String
  for e: {Laws.distinct(packs) == True{} : Bool}
  {Laws.distinct(P.walk.packs(P.step.pop(orgs, js, queue, packs, asks, bad)))
    == True{} : Bool}

def pop_distinct(orgs, js, queue, packs, asks, bad, e):
  match queue:
    case []:
      e
    case +h <> t:
      pick_distinct(Bool.or(L.has(packs, h), L.seen.holds(asks, h)), orgs, js,
        h, t, packs, asks, bad, e, {==})

# LAW: one step keeps every resolved hash distinct
law step_distinct:
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for wk: P.Walk
  for e: {Laws.distinct(P.walk.packs(wk)) == True{} : Bool}
  {Laws.distinct(P.walk.packs(P.walk.step(orgs, js, wk))) == True{} : Bool}

def step_distinct(orgs, js, wk, e):
  match wk:
    case P.Walk{queue, packs, asks, bad}:
      pop_distinct(orgs, js, queue, packs, asks, bad, e)

# LAW: a walk that ran out of fuel keeps the packages it had
law out_distinct:
  for done: Bool
  for wk: P.Walk
  for e: {Laws.distinct(P.walk.packs(wk)) == True{} : Bool}
  {Laws.distinct(P.walk.packs(P.walk.out(done, wk))) == True{} : Bool}

def out_distinct(done, wk, e):
  match done:
    case True{}:
      e
    case False{}:
      match wk:
        case P.Walk{_queue, _packs, _asks, _bad}:
          e

# LAW: a walk that is done is what it was, and one that is not goes on
law more_distinct:
  for done: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for f: Nat
  for +wk: P.Walk
  for e: {Laws.distinct(P.walk.packs(wk)) == True{} : Bool}
  for ih: {Laws.distinct(P.walk.packs(P.walk(f, orgs, js,
    P.walk.step(orgs, js, wk)))) == True{} : Bool}
  {Laws.distinct(P.walk.packs(P.walk.more(done, wk,
    now => P.walk(f, orgs, js, P.walk.step(orgs, js, now))))) == True{} : Bool}

def more_distinct(done, _orgs, _js, _f, _wk, e, ih):
  match done:
    case True{}:
      e
    case False{}:
      ih

def Laws.walk_keeps_hashes_distinct(fuel, orgs, js, wk, e):
  match fuel:
    case 0n:
      out_distinct(P.walk.done(wk), wk, e)
    case 1n+f:
      more_distinct(P.walk.done(wk), orgs, js, f, wk, e,
        Laws.walk_keeps_hashes_distinct(f, orgs, js, P.walk.step(orgs, js, wk),
          step_distinct(orgs, js, wk, e)))

# LAW: the walk from any listing, over any ledger and verdicts, resolves each
# hash once
law walk_of_distinct:
  for +led: M.Read
  for listing: W.Listing
  for +js: List<&2, W.Judged>
  {Laws.distinct(P.walk.packs(P.walk.of(led, listing, js))) == True{} : Bool}

def walk_of_distinct(led, listing, js):
  match listing:
    case W.Unlisted{why}:
      {==}
    case W.Listed{fs}:
      Laws.walk_keeps_hashes_distinct(U32.to_nat(100000), L.ledger.read(led), js,
        P.Walk{P.roots(fs), [], [], ""}, {==})

# The walk is the same for a plain lock and an upgrade; only the ledger, the
# listing and the verdicts it walks over differ.
def Laws.plain_lock_hashes_distinct(w):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      walk_of_distinct(Up.next.read(W.next(args, ledger, ups)),
        W.listing.of(W.next(args, ledger, ups), listing),
        W.judged.of(W.next(args, ledger, ups), replies))

# `.ez/` is a prefix of anything appended to it, which `starts_append` holds,
# and that picks the arm that keeps nothing.
def Laws.root_skips_ez(p, text):
  Equal.cong(Bool, List<&2, String>,
    k => Bool.pick(List<&2, String>, k, [], L.specs(K.scan.mods(K.scan(text)))),
    String.starts_with(".ez/" ++ p, ".ez/"), True{}, Eq.starts_append(".ez/", p))

# Idempotence. A clone that passed weighed to the narHash the ledger records,
# so the same bytes read from BEND_LIB, which are judged as a clone weighed to
# that narHash (`lib_as_clone.src`), pass the same way. Every verdict is what
# it was, so the Inputs are, and `lock_reproducible` gives the rest.

# LAW: a weighed git package that passed was weighed with no reason to refuse
law weighed_passes:
  for why: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {Laws.passed(W.git.weighed(why, hash, manifest, ss)) == True{} : Bool}
  {why == "" : String}

def weighed_passes(why, _hash, _manifest, _ss, e):
  match why:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Eq.bit.absurd(&2, {SCon{h, t} == "" : String}, e)

# LAW: a checkout whose NAR hash the ledger agreed with has a NAR hash the
# ledger records, so the ledger's own agrees with it too
law nar_agrees_when_passed:
  for +nar: String
  for +got: String
  for +url: String
  for +rev: String
  for e: {L.nar.why(nar, got, url, rev) == "" : String}
  {L.nar.why(nar, nar, url, rev) == "" : String}

def nar_agrees_when_passed(nar, got, url, rev, e):
  match nar:
    case SNil{}:
      Eq.bit.absurd(&2, {L.nar.why("", "", url, rev) == "" : String},
        Equal.cong(String, Bool, s => String.is_empty(s),
          L.nar.why("", got, url, rev), "", e))
    case SCon{+h, +t}:
      Laws.nar_why_agrees(SCon{h, t}, url, rev, {==})

# LAW: a clone that passed is judged as the same bytes read from BEND_LIB
law clone_passed.src:
  for src: L.Src
  for +got: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {Laws.passed(W.accept.src(src, W.Clone{got}, hash, manifest, ss)) == True{} : Bool}
  {W.accept.src(src, W.Lib{}, hash, manifest, ss)
    == W.accept.src(src, W.Clone{got}, hash, manifest, ss) : W.Verdict}

def clone_passed.src(src, got, hash, manifest, ss, e):
  match src:
    case L.Hub{}:
      Eq.bit.absurd(&2, {W.accept.src(L.Hub{}, W.Lib{}, hash, manifest, ss)
        == W.accept.src(L.Hub{}, W.Clone{got}, hash, manifest, ss) : W.Verdict}, e)
    case L.Git{+url, +rev, _entry, _root, +nar, _tag}:
      +same = weighed_passes(L.nar.why(nar, got, url, rev), hash, manifest, ss, e)
      Equal.trans(W.Verdict,
        W.git.weighed(L.nar.why(nar, nar, url, rev), hash, manifest, ss),
        W.git.weighed("", hash, manifest, ss),
        W.git.weighed(L.nar.why(nar, got, url, rev), hash, manifest, ss),
        Equal.cong(String, W.Verdict, why => W.git.weighed(why, hash, manifest, ss),
          L.nar.why(nar, nar, url, rev), "",
          nar_agrees_when_passed(nar, got, url, rev, same)),
        Equal.sym(W.Verdict,
          W.git.weighed(L.nar.why(nar, got, url, rev), hash, manifest, ss),
          W.git.weighed("", hash, manifest, ss),
          Equal.cong(String, W.Verdict, why => W.git.weighed(why, hash, manifest, ss),
            L.nar.why(nar, got, url, rev), "", same)))

# LAW: a cloned tree, laid when it passed, is judged as it was
law after.clone_judged:
  for b: Bool
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for +got: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {Laws.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})) == b
    : Bool}
  {W.accept(orgs, hub, hash, Laws.after.clone(b, got, manifest, ss))
    == W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss}) : W.Verdict}

def after.clone_judged(b, orgs, _hub, hash, got, manifest, ss, e):
  match b:
    case True{}:
      clone_passed.src(L.origin(orgs, hash), got, hash, manifest, ss, e)
    case False{}:
      {==}

# LAW: one answer, as the next lock reads it, is judged as it was
law after.one_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {W.accept(orgs, hub, hash, Laws.after.one(orgs, hub, hash, a))
    == W.accept(orgs, hub, hash, a) : W.Verdict}

def after.one_judged(orgs, hub, hash, a):
  match a:
    case W.Miss{_why}:
      {==}
    case W.Got{how, +manifest, +ss}:
      match how:
        case W.Lib{}:
          {==}
        case W.Clone{+got}:
          after.clone_judged(
            Laws.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
            orgs, hub, hash, got, manifest, ss, {==})
        case W.Served{}:
          {==}

# LAW: every answer, as the next lock reads it, is judged as it was
law after_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {W.judge(orgs, hub, Laws.after.all(orgs, hub, rs)) == W.judge(orgs, hub, rs)
    : List<&2, W.Judged>}

def after_judged(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+ask, a} <> t:
      Equal.trans(List<&2, W.Judged>,
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask),
          Laws.after.one(orgs, hub, W.ask.hash(ask), a))}
          <> W.judge(orgs, hub, Laws.after.all(orgs, hub, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, Laws.after.all(orgs, hub, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, t),
        Equal.cong(W.Verdict, List<&2, W.Judged>,
          v => W.Judged{W.ask.hash(ask), v}
            <> W.judge(orgs, hub, Laws.after.all(orgs, hub, t)),
          W.accept(orgs, hub, W.ask.hash(ask),
            Laws.after.one(orgs, hub, W.ask.hash(ask), a)),
          W.accept(orgs, hub, W.ask.hash(ask), a),
          after.one_judged(orgs, hub, W.ask.hash(ask), a)),
        Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
          js => W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)} <> js,
          W.judge(orgs, hub, Laws.after.all(orgs, hub, t)),
          W.judge(orgs, hub, t),
          after_judged(orgs, hub, t)))

# LAW: the World a lock that succeeded leaves has the Inputs it read
law after.laid_inputs:
  for w: W.World
  {W.inputs(Laws.after.laid(w)) == W.inputs(w) : W.Inputs}

def after.laid_inputs(w):
  match w:
    case W.World{+args, +ledger, listing, replies, +ups}:
      Equal.cong(List<&2, W.Judged>, W.Inputs,
        js => W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          List.append(&2, W.Judged,
            W.judge(W.next.origins(W.next(args, ledger, ups)),
              W.next.hub(W.next(args, ledger, ups)),
              W.laid.replies(Up.next.trees(W.next(args, ledger, ups)),
                W.next.origins(W.next(args, ledger, ups)),
                W.next.hub(W.next(args, ledger, ups)))), js)},
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)),
          Laws.after.all(W.next.origins(W.next(args, ledger, ups)),
            W.next.hub(W.next(args, ledger, ups)), replies)),
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies),
        after_judged(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies))

# LAW: whether or not the lock refused, the World it leaves writes its lock
law after.pick_put:
  for b: Bool
  for +w: W.World
  {P.put(Laws.after.pick(b, w), "ez.lock.toml") == P.put(w, "ez.lock.toml")
    : P.Wrote}

def after.pick_put(b, w):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.lock_reproducible(Laws.after.laid(w), w, after.laid_inputs(w))

def Laws.lock_idempotent(w):
  after.pick_put(P.refuses(w), w)

# LAW: a cloned tree, as the next lock reads it, is not one it lays: laid, it
# is read from BEND_LIB, and not laid, it failed
law fresh.clone:
  for b: Bool
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for +got: String
  for +manifest: String
  for +ss: List<&2, String>
  for e: {Laws.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})) == b
    : Bool}
  {Laws.fresh.one(orgs, hub, hash, Laws.after.clone(b, got, manifest, ss)) == []
    : List<&2, String>}

def fresh.clone(b, orgs, hub, hash, got, manifest, ss, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, List<&2, String>,
        x => Bool.pick(List<&2, String>, x, [hash], []),
        Laws.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
        False{}, e)

# LAW: no answer, as the next lock reads it, is a tree it lays
law fresh.one_after:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {Laws.fresh.one(orgs, hub, hash, Laws.after.one(orgs, hub, hash, a)) == []
    : List<&2, String>}

def fresh.one_after(orgs, hub, hash, a):
  match a:
    case W.Miss{_why}:
      {==}
    case W.Got{how, +manifest, +ss}:
      match how:
        case W.Lib{}:
          {==}
        case W.Clone{+got}:
          fresh.clone(
            Laws.passed(W.accept(orgs, hub, hash, W.Got{W.Clone{got}, manifest, ss})),
            orgs, hub, hash, got, manifest, ss, {==})
        case W.Served{}:
          {==}

# LAW: and none of them is
law fresh.all_after:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {Laws.fresh.all(orgs, hub, Laws.after.all(orgs, hub, rs)) == [] : List<&2, String>}

def fresh.all_after(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+ask, a} <> t:
      Equal.trans(List<&2, String>,
        List.append(&2, String,
          Laws.fresh.one(orgs, hub, W.ask.hash(ask),
            Laws.after.one(orgs, hub, W.ask.hash(ask), a)),
          Laws.fresh.all(orgs, hub, Laws.after.all(orgs, hub, t))),
        Laws.fresh.all(orgs, hub, Laws.after.all(orgs, hub, t)),
        [],
        Equal.cong(List<&2, String>, List<&2, String>,
          x => List.append(&2, String, x,
            Laws.fresh.all(orgs, hub, Laws.after.all(orgs, hub, t))),
          Laws.fresh.one(orgs, hub, W.ask.hash(ask),
            Laws.after.one(orgs, hub, W.ask.hash(ask), a)),
          [],
          fresh.one_after(orgs, hub, W.ask.hash(ask), a)),
        fresh.all_after(orgs, hub, t))

# LAW: the World a lock that succeeded leaves has no tree for the next to lay
law fresh.laid:
  for w: W.World
  {Laws.fresh(Laws.after.laid(w)) == [] : List<&2, String>}

def fresh.laid(w):
  match w:
    case W.World{+args, +ledger, _listing, replies, +ups}:
      fresh.all_after(W.next.origins(W.next(args, ledger, ups)),
        W.next.hub(W.next(args, ledger, ups)), replies)

def Laws.relock_lays_nothing(w, ok):
  Equal.trans(List<&2, String>,
    Laws.fresh(Laws.after.pick(P.refuses(w), w)),
    Laws.fresh(Laws.after.pick(False{}, w)),
    [],
    Equal.cong(Bool, List<&2, String>, b => Laws.fresh(Laws.after.pick(b, w)),
      P.refuses(w), False{}, ok),
    fresh.laid(w))

# The lock document's first step. The lemmas are about lists of chars, since
# eztoml's trim and strip walk a string as one; the list lemmas are
# check/str.bend's.

# LAW: a trim that has stopped skipping keeps every char, reversed onto what
# it kept already
law walk_kept:
  for +xs: List<&2, Char>
  for +acc: List<&2, Char>
  {T.trim.walk(xs, T.Trim{False{}, acc})
    == T.Trim{False{}, List.reverse.go(&2, Char, xs, acc)} : T.Trim}

def walk_kept(xs, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_kept(t, h <> acc)

# LAW: the first pass over a quoted value
law trim_quoted.first:
  for +v: String
  {T.trim.pass(String.to_list(T.quote(v)))
    == '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"'])
    : List<&2, Char>}

def trim_quoted.first(v):
  Equal.trans(List<&2, Char>,
    T.trim.pass(String.to_list(T.quote(v))),
    List.reverse.go(&2, Char,
      List.append(&2, Char, String.to_list(v), ['"']), ['"']),
    '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"']),
    Equal.trans(List<&2, Char>,
      T.trim.pass(String.to_list(T.quote(v))),
      T.trim.out(T.trim.walk(
        List.append(&2, Char, String.to_list(v), ['"']),
        T.Trim{False{}, ['"']})),
      List.reverse.go(&2, Char,
        List.append(&2, Char, String.to_list(v), ['"']), ['"']),
      Equal.cong(List<&2, Char>, List<&2, Char>,
        cs => T.trim.out(T.trim.walk(cs, T.Trim{False{}, ['"']})),
        String.to_list(String.append(v, "\"")),
        List.append(&2, Char, String.to_list(v), ['"']),
        Str.to_list_append(v, "\"")),
      Equal.cong(T.Trim, List<&2, Char>, st => T.trim.out(st),
        T.trim.walk(List.append(&2, Char, String.to_list(v), ['"']),
          T.Trim{False{}, ['"']}),
        T.Trim{False{}, List.reverse.go(&2, Char,
          List.append(&2, Char, String.to_list(v), ['"']), ['"'])},
        walk_kept(List.append(&2, Char, String.to_list(v), ['"']), ['"']))),
    Str.rev_append(String.to_list(v), ['"'], ['"']))

# LAW: the two passes of a trim over a quoted value, as reversals
law trim_quoted.passes:
  for +v: String
  {T.trim(T.quote(v))
    == String.from_list(List.reverse.go(&2, Char,
      List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])) : String}

def trim_quoted.passes(v):
  Equal.trans(String,
    T.trim(T.quote(v)),
    String.from_list(T.trim.pass(
      '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"']))),
    String.from_list(List.reverse.go(&2, Char,
      List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])),
    Equal.cong(List<&2, Char>, String,
      cs => String.from_list(T.trim.pass(cs)),
      T.trim.pass(String.to_list(T.quote(v))),
      '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"']),
      trim_quoted.first(v)),
    Equal.cong(T.Trim, String, st => String.from_list(T.trim.out(st)),
      T.trim.walk(List.reverse.go(&2, Char, String.to_list(v), ['"']),
        T.Trim{False{}, ['"']}),
      T.Trim{False{}, List.reverse.go(&2, Char,
        List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])},
      walk_kept(List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])))

# The trim of a quoted value, one pass at a time. The first pass keeps the
# opening quote and so everything after it, reversed; the second keeps the
# closing quote, now first, and reverses the rest back.
def Laws.trim_quoted(v):
  Equal.trans(String,
    T.trim(T.quote(v)),
    String.from_list(List.reverse.go(&2, Char,
      List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])),
    T.quote(v),
    trim_quoted.passes(v),
    Equal.trans(String,
      String.from_list(List.reverse.go(&2, Char,
        List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])),
      String.from_list('"' <> List.append(&2, Char, String.to_list(v), ['"'])),
      T.quote(v),
      Equal.cong(List<&2, Char>, String, cs => String.from_list(cs),
        List.reverse.go(&2, Char,
          List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"']),
        '"' <> List.append(&2, Char, String.to_list(v), ['"']),
        Str.rev_rev(String.to_list(v), ['"'], ['"'])),
      Equal.cong(String, String, s => SCon{'"', s},
        String.from_list(List.append(&2, Char, String.to_list(v), ['"'])),
        String.append(v, "\""),
        Str.from_to_append(v, ['"']))))

# LAW: the walk that drops a trailing quote, one char behind the list it
# walks
law back_go_quote:
  for +t: List<&2, Char>
  for +h: Char
  {T.strip.back.go(List.append(&2, Char, t, ['"']), h, '"') == h <> t
    : List<&2, Char>}

def back_go_quote(t, h):
  match t:
    case []:
      {==}
    case +h2 <> +t2:
      Equal.cong(List<&2, Char>, List<&2, Char>, cs => h <> cs,
        T.strip.back.go(List.append(&2, Char, t2, ['"']), h2, '"'),
        h2 <> t2,
        back_go_quote(t2, h2))

# LAW: a list that ends in a quote, with the quote dropped
law back_quote:
  for +xs: List<&2, Char>
  {T.strip.back(List.append(&2, Char, xs, ['"']), '"') == xs
    : List<&2, Char>}

def back_quote(xs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      back_go_quote(t, h)

def Laws.strip_quoted(v):
  Equal.trans(String,
    T.strip(T.quote(v), '"', '"'),
    String.from_list(T.strip.back(
      List.append(&2, Char, String.to_list(v), ['"']), '"')),
    v,
    Equal.cong(List<&2, Char>, String,
      cs => String.from_list(T.strip.back(cs, '"')),
      String.to_list(String.append(v, "\"")),
      List.append(&2, Char, String.to_list(v), ['"']),
      Str.to_list_append(v, "\"")),
    Equal.trans(String,
      String.from_list(T.strip.back(
        List.append(&2, Char, String.to_list(v), ['"']), '"')),
      String.from_list(String.to_list(v)),
      v,
      Equal.cong(List<&2, Char>, String, cs => String.from_list(cs),
        T.strip.back(List.append(&2, Char, String.to_list(v), ['"']), '"'),
        String.to_list(v),
        back_quote(String.to_list(v))),
      Str.from_to(v)))

# The upgrade's moves (EZ-RES-5, EZ-RES-8). Each law is one fact about one
# dependency's fate (`Up.dep.one`), carried through the walk over the ledger's
# dependencies (`Up.deps.walk`) to the ledger model the upgrade renders
# (`Up.next.model`). A fate is proved sound once for any remote tip, since a
# tag's and the default branch's are read the same way from there on
# (`Up.dep.tip`).

# a pin from a repository, with its fields spelled out
def mv.git(+hn: String, +hh: String, +he: String, +url: String, +rev: String, +tag: String,
  +root: String, +nar: String, +vend: Bool) -> M.Dep:
  M.Dep{hn, hh, he, M.Git{url, rev, tag, root, nar, vend}}

# a fate is sound against a tip when the pin it leaves is kept or moved
# along its history, as `moved.ok` reads the remote
def mv.ok(fate: Up.Fate, +t: Up.Tip, +rs: List<&2, Up.Reply>, +old: M.Dep) -> Bool:
  match fate:
    case Up.Became{d, _o, _n, _p, _m, _s, _t}:
      Laws.moved.ok(t, rs, old, d)
    case Up.Waits{_asks}:
      True{}
    case Up.Halts{_why}:
      True{}

# what every fate keeps: the name of the dependency it leaves, and at least
# one question when it waits
def mv.fine(fate: Up.Fate, +name: String) -> String & Bool:
  match fate:
    case Up.Became{d, _o, _n, _p, _m, _s, _t}:
      (M.dep.name(d), True{})
    case Up.Waits{asks}:
      (name, Bool.not(List.is_empty(&2, Up.Ask, asks)))
    case Up.Halts{_why}:
      (name, True{})

# whether a fate refuses
def mv.halts(fate: Up.Fate) -> Bool:
  match fate:
    case Up.Became{_d, _o, _n, _p, _m, _s, _t}:
      False{}
    case Up.Waits{_asks}:
      False{}
    case Up.Halts{_why}:
      True{}

# the walk is sound for the dependency named `n`: it refuses, or still asks,
# or the dependency it leaves under that name is sound against `old`
def mv.walk(+t: Up.Tip, +rs: List<&2, Up.Reply>, dd: Up.Deps, +old: M.Dep, +n: String) -> Bool:
  Up.Deps{ds, _ss, _es, _m, _sy, _tr, asks, bad} = dd
  Bool.or(Bool.not(String.is_empty(bad)),
    Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)), Laws.moved.ok(t, rs, old, M.find(ds, n))))

# the walk's refusal, "" for none
def mv.bad(dd: Up.Deps) -> String:
  Up.Deps{_ds, _ss, _es, _m, _sy, _tr, _asks, bad} = dd
  bad

# whether an upgrade refuses
def mv.stops(nx: Up.Next) -> Bool:
  Bool.not(String.is_empty(Up.next.stop(nx)))

# the dependency named `n` in the ledger model an upgrade renders
def mv.dep(nx: Up.Next, +n: String) -> M.Dep:
  M.dep(Up.next.model(nx), n)

def mv.fst(p: String & Bool) -> String:
  (a, _b) = p
  a

def mv.snd(p: String & Bool) -> Bool:
  (_a, b) = p
  b

# LAW: an `or` whose right half answered True
law mv.or_r:
  for a: Bool
  for b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def mv.or_r(a, _b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

# LAW: an `or` whose left half answered True
law mv.or_l:
  for a: Bool
  for +b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def mv.or_l(a, b, e):
  Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, e)

# LAW: a refusal's reason is never empty
law mv.halt_ne:
  for why: String
  {String.is_empty(Up.halt.why(why)) == False{} : Bool}

def mv.halt_ne(why):
  match why:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# LAW: and so it reads as a refusal
law mv.halt_not:
  for why: String
  {Bool.not(String.is_empty(Up.halt.why(why))) == True{} : Bool}

def mv.halt_not(why):
  match why:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# LAW: a pin kept as it was is sound against any tip
law mv.self:
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {Laws.moved.ok(t, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend),
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.self(t, rs, _hn, _hh, _he, url, rev, tag, _root, _nar, _vend):
  Equal.trans(Bool,
    Bool.and(String.eq(tag, tag),
      Bool.or(String.eq(rev, rev), Laws.moved.to(t, rs, url, rev, rev))),
    Bool.or(String.eq(rev, rev), Laws.moved.to(t, rs, url, rev, rev)),
    True{},
    Equal.cong(Bool, Bool,
      x => Bool.and(x, Bool.or(String.eq(rev, rev), Laws.moved.to(t, rs, url, rev, rev))),
      String.eq(tag, tag), True{}, Eq.string_eq_self(tag)),
    Equal.cong(Bool, Bool, x => Bool.or(x, Laws.moved.to(t, rs, url, rev, rev)),
      String.eq(rev, rev), True{}, Eq.string_eq_self(rev)))

# LAW: and so is any pin from a repository
law mv.self_dep:
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +d: M.Dep
  for g: {M.source.is_git(M.source.dep(d)) == True{} : Bool}
  {Laws.moved.ok(t, rs, d, d) == True{} : Bool}

def mv.self_dep(t, rs, d, g):
  match d:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          g
        case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
          mv.self(t, rs, hn, hh, he, url, rev, tag, root, nar, vend)

# LAW: a pin by its commit alone is from a repository
law mv.bare_git:
  for +d: M.Dep
  for bare: {Laws.rev_only(d) == True{} : Bool}
  {M.source.is_git(M.source.dep(d)) == True{} : Bool}

def mv.bare_git(d, bare):
  match d:
    case M.Dep{_hn, _hh, _he, src}:
      match src:
        case M.Hub{}:
          bare
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          {==}

# LAW: and so is one through a tag
law mv.named_git:
  for +d: M.Dep
  for named: {Laws.tagged(d) == True{} : Bool}
  {M.source.is_git(M.source.dep(d)) == True{} : Bool}

def mv.named_git(d, named):
  match d:
    case M.Dep{_hn, _hh, _he, src}:
      match src:
        case M.Hub{}:
          named
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          {==}

# One pin's fate is sound against the tip it was moved by. The pin is
# checked out when the tip is its own commit, and kept only when the checkout
# agrees; it is moved only to a tip the remote says descends from it, once
# the tip's checkout and the hub's word are in.

# LAW: a pin moved to the tip, once the hub has not objected
law mv.ok_hub:
  for hb: Up.Hubbed
  for +rs: List<&2, Up.Reply>
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +hash: String
  for +r: String
  for +tg: String
  for +br: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  for e: {Up.onward(rs, Up.Above{url, rev, r}) == Up.Asc{True{}} : Up.Asc}
  {mv.ok(Up.dep.hub(hb, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), hash, r, root2,
    nar2, man, srcs, br), Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend))
    == True{} : Bool}

def mv.ok_hub(hb, rs, _hn, _hh, _he, url, rev, tag, _root, _nar, _vend, _hash, r, _tg, _br,
  _root2, _nar2, _man, _srcs, e):
  match hb:
    case Up.Clear{}:
      Equal.trans(Bool,
        Bool.and(String.eq(tag, tag), Bool.or(String.eq(r, rev),
          Bool.and(String.eq(r, r), Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))))),
        Bool.or(String.eq(r, rev),
          Bool.and(String.eq(r, r), Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r})))),
        True{},
        Equal.cong(Bool, Bool, x => Bool.and(x, Bool.or(String.eq(r, rev),
          Bool.and(String.eq(r, r), Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))))),
          String.eq(tag, tag), True{}, Eq.string_eq_self(tag)),
        mv.or_r(String.eq(r, rev),
          Bool.and(String.eq(r, r), Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))),
          Equal.trans(Bool,
            Bool.and(String.eq(r, r), Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))),
            Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r})),
            True{},
            Equal.cong(Bool, Bool,
              x => Bool.and(x, Laws.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))),
              String.eq(r, r), True{}, Eq.string_eq_self(r)),
            Equal.cong(Up.Asc, Bool, a => Laws.onward.yes(a),
              Up.onward(rs, Up.Above{url, rev, r}), Up.Asc{True{}}, e))))
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved to the tip, once its checkout is in
law mv.ok_adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  for e: {Up.onward(rs, Up.Above{url, rev, r}) == Up.Asc{True{}} : Up.Asc}
  {mv.ok(Up.dep.advance(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, br),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_adv(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br, e):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      mv.ok_hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), rs, hn, hh, he, url, rev, tag,
        root, nar, vend, Up.hash.of(man), r, tg, br, root2, nar2, man, srcs, e)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: a tip that is another commit, once the remote said whether it
# descends from the pin
law mv.ok_onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  for e: {Up.onward(rs, Up.Above{url, rev, r}) == a : Up.Asc}
  {mv.ok(Up.dep.onward(a, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, tg, br),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_onward(a, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br, e):
  match a:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          mv.ok_adv(Up.checkout(rs, Up.Tree{url, r, he}), rs, hub, hn, hh, he, url, rev, tag,
            root, nar, vend, r, tg, br, e)
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the pin's own commit, judged by whether its checkout agrees
law mv.ok_agree:
  for g: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  for +seen: String
  {mv.ok(Up.dep.verdict(U.judge(True{}, True{}, g, r, tg), rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, "", seen),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_agree(g, rs, _hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br, _seen):
  match g:
    case True{}:
      mv.self(Up.At{r, tg, br}, rs, hn, hh, he, url, rev, tag, root, nar, vend)
    case False{}:
      {==}

# LAW: the pin's own commit, once its checkout is in
law mv.ok_kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  {mv.ok(Up.dep.kept(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, tg),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_kept(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      mv.ok_agree(U.agree(hh, Up.hash.of(man), nar, nar2, root, root2), rs, hub, hn, hh, he,
        url, rev, tag, root, nar, vend, r, tg, br, Up.hash.of(man))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: the tip against the pin: its own commit, or another
law mv.ok_same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  {mv.ok(Up.dep.same(s, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, tg, br),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_same(s, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br):
  match s:
    case True{}:
      mv.ok_kept(Up.checkout(rs, Up.Tree{url, rev, he}), rs, hub, hn, hh, he, url, rev, tag,
        root, nar, vend, r, tg, br)
    case False{}:
      mv.ok_onward(Up.onward(rs, Up.Above{url, rev, r}), rs, hub, hn, hh, he, url, rev, tag,
        root, nar, vend, r, tg, br, {==})

# LAW: a pin is sound against whatever tip the remote named
law mv.ok_tip:
  for t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {mv.ok(Up.dep.tip(t, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)), t, rs,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_tip(t, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend):
  match t:
    case Up.At{+r, +tg, +br}:
      mv.ok_same(String.eq(rev, r), rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# Every fate keeps its dependency's name, and waits only with a question. The
# walk reads the name to find a dependency again, and a question to tell a
# walk that waits from one that is done.

# LAW: a pin moved, once the hub has had its word
law mv.fine_hub:
  for hb: Up.Hubbed
  for +hn: String
  for +hh: String
  for +he: String
  for src: M.Source
  for +hash: String
  for +r: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  for +br: String
  {mv.fine(Up.dep.hub(hb, M.Dep{hn, hh, he, src}, hash, r, root2, nar2, man, srcs, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_hub(hb, _hn, _hh, _he, src, _hash, _r, _root2, _nar2, _man, _srcs, _br):
  match hb:
    case Up.Clear{}:
      match src:
        case M.Hub{}:
          {==}
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          {==}
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved, once its checkout is in
law mv.fine_adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +r: String
  for +br: String
  {mv.fine(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, src}, r, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_adv(co, rs, hub, hn, hh, he, src, r, br):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      mv.fine_hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), hn, hh, he, src,
        Up.hash.of(man), r, root2, nar2, man, srcs, br)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: any verdict
law mv.fine_verdict:
  for v: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +br: String
  for +seen: String
  {mv.fine(Up.dep.verdict(v, rs, hub, M.Dep{hn, hh, he, src}, tip, br, seen), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_verdict(v, rs, hub, hn, hh, he, src, _tip, br, _seen):
  match v:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rv, _tg}:
      mv.fine_adv(Up.checkout(rs, Up.Tree{M.source.url(src), rv, he}), rs, hub, hn, hh, he, src,
        rv, br)

# LAW: the pin's own commit, once its checkout is in
law mv.fine_kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  {mv.fine(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, src}, tip, tg), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_kept(co, rs, hub, hn, hh, he, src, tip, tg):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      mv.fine_verdict(U.judge(True{}, True{}, U.agree(hh, Up.hash.of(man), M.source.nar(src),
        nar2, M.source.root(src), root2), tip, tg), rs, hub, hn, hh, he, src, tip, "",
        Up.hash.of(man))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: another commit, once ancestry is in
law mv.fine_onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  for +br: String
  {mv.fine(Up.dep.onward(a, rs, hub, M.Dep{hn, hh, he, src}, tip, tg, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_onward(a, rs, hub, hn, hh, he, src, tip, tg, br):
  match a:
    case Up.Asc{yes}:
      mv.fine_verdict(U.judge(False{}, yes, False{}, tip, tg), rs, hub, hn, hh, he, src, tip, br, "")
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the tip against the pin
law mv.fine_same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  for +br: String
  {mv.fine(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, src}, tip, tg, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_same(s, rs, hub, hn, hh, he, src, tip, tg, br):
  match s:
    case True{}:
      mv.fine_kept(Up.checkout(rs, Up.Tree{M.source.url(src), M.source.rev(src), he}), rs, hub,
        hn, hh, he, src, tip, tg)
    case False{}:
      mv.fine_onward(Up.onward(rs, Up.Above{M.source.url(src), M.source.rev(src), tip}), rs, hub,
        hn, hh, he, src, tip, tg, br)

# LAW: whatever tip the remote named
law mv.fine_tip:
  for t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  {mv.fine(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, src}), hn) == (hn, True{}) : String & Bool}

def mv.fine_tip(t, rs, hub, hn, hh, he, src):
  match t:
    case Up.At{+tip, +tg, +br}:
      mv.fine_same(String.eq(M.source.rev(src), tip), rs, hub, hn, hh, he, src, tip, tg, br)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: every dependency's fate, whatever it was asked
law mv.fine_one:
  for am: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  {mv.fine(Up.dep.one(am, rs, only, hub, h), M.dep.name(h))
    == (M.dep.name(h), True{}) : String & Bool}

def mv.fine_one(am, rs, only, hub, h):
  match am h:
    case U.Hold{} M.Dep{_hn, _hh, _he, _src}:
      {==}
    case U.Follow{+ref} M.Dep{+hn, +hh, +he, +src}:
      mv.fine_tip(Up.follow(rs, M.source.url(src), ref), rs, hub, hn, hh, he, src)
    case U.Forward{} M.Dep{+hn, +hh, +he, +src}:
      mv.fine_tip(Up.forward(rs, M.source.url(src)), rs, hub, hn, hh, he, src)

# One pin's fate from what it was asked. A pin by its commit alone follows the
# default branch when it is asked about, and one through a tag its tag; one
# that is not asked about is held.

# LAW: a pin by its commit alone, asked about or not
law mv.fwd_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {mv.ok(Up.dep.one(U.aim(s, M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, "", root, nar, vend)), Up.forward(rs, url), rs,
    mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}

def mv.fwd_sel(s, rs, _only, hub, hn, hh, he, url, rev, root, nar, vend):
  match s:
    case False{}:
      mv.self(Up.forward(rs, url), rs, hn, hh, he, url, rev, "", root, nar, vend)
    case True{}:
      mv.ok_tip(Up.forward(rs, url), rs, hub, hn, hh, he, url, rev, "", root, nar, vend)

# LAW: a pin by its commit alone moves only along the default branch
law mv.fwd_one:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for bare: {Laws.rev_only(h) == True{} : Bool}
  {mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    Up.forward(rs, M.source.url(M.source.dep(h))), rs, h) == True{} : Bool}

def mv.fwd_one(rs, only, hub, h, bare):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.ok(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}}), Up.forward(rs, ""), rs, M.Dep{hn, hh, he, M.Hub{}})
            == True{} : Bool}, bare)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              mv.fwd_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, root, nar, vend)
            case SCon{+c, +ct}:
              Eq.bit.absurd(&2, {mv.ok(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), Up.forward(rs, url), rs,
                mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}, bare)

# LAW: a pin through a tag, asked about or not
law mv.fol_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {mv.ok(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), Up.follow(rs, url, SCon{c, ct}),
    rs, mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}

def mv.fol_sel(s, rs, _only, hub, hn, hh, he, url, rev, c, ct, root, nar, vend):
  match s:
    case False{}:
      mv.self(Up.follow(rs, url, SCon{c, ct}), rs, hn, hh, he, url, rev, SCon{c, ct}, root, nar,
        vend)
    case True{}:
      mv.ok_tip(Up.follow(rs, url, SCon{c, ct}), rs, hub, hn, hh, he, url, rev, SCon{c, ct},
        root, nar, vend)

# LAW: a pin through a tag moves only to what the tag names, along its history
law mv.fol_one:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for named: {Laws.tagged(h) == True{} : Bool}
  {mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h))), rs, h)
    == True{} : Bool}

def mv.fol_one(rs, only, hub, h, named):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.ok(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}}), Up.follow(rs, "", ""), rs, M.Dep{hn, hh, he, M.Hub{}})
            == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {mv.ok(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, "", root, nar, vend)), Up.follow(rs, url, ""), rs,
                mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root, nar,
                vend)

# The walk over the ledger's dependencies. `M.find` answers the first
# dependency of a name, and every fate keeps its name, so the walk leaves the
# named dependency where the ledger had it, unless it refused or still asks.

# LAW: a walk over no dependencies: the blank pin `M.find` answers is never
# sound, so neither side holds
law mv.walk_nil:
  for s: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for pre: {mv.ok(Up.dep.one(U.aim(s, M.Hub{}), rs, only, hub, M.Dep{"", "", "", M.Hub{}}), t, rs,
    M.Dep{"", "", "", M.Hub{}}) == True{} : Bool}
  {mv.walk(t, rs, Up.deps.walk(rs, only, hub, []), M.Dep{"", "", "", M.Hub{}}, n) == True{} : Bool}

def mv.walk_nil(s, _t, _rs, _only, _hub, _n, pre):
  match s:
    case True{}:
      pre
    case False{}:
      pre

# LAW: the named dependency's fate in front of the rest
law mv.join_hit:
  for f: Up.Fate
  for rest: Up.Deps
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for e: {String.eq(hn, n) == True{} : Bool}
  for ok: {mv.ok(f, t, rs, M.Dep{hn, hh, he, src}) == True{} : Bool}
  for fn: {mv.fine(f, hn) == (hn, True{}) : String & Bool}
  {mv.walk(t, rs, Up.deps.join(f, rest), M.Dep{hn, hh, he, src}, n) == True{} : Bool}

def mv.join_hit(f, rest, t, rs, n, hn, hh, he, src, e, ok, fn):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _o, _nw, _pv, _m, _sy, _tr} Up.Deps{+ds, _ss, _es, _any, _sy2, _tr2, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src},
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src},
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src},
                M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          dn, hn, Equal.cong(String & Bool, String, p => mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src},
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.Dep{dn, dh, de, dsrc}))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)),
              Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
                Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src},
                  M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
            String.eq(hn, n), True{}, e),
          mv.or_r(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.Dep{dn, dh, de, dsrc})),
            mv.or_r(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.Dep{dn, dh, de, dsrc}), ok))))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.find(ds, n)))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, _bad}:
      mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.find(ds, n))),
        mv.halt_not(why))

# LAW: another dependency's fate in front of the rest
law mv.join_miss:
  for f: Up.Fate
  for rest: Up.Deps
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hn: String
  for +old: M.Dep
  for e: {String.eq(hn, n) == False{} : Bool}
  for fn: {mv.fine(f, hn) == (hn, True{}) : String & Bool}
  for ih: {mv.walk(t, rs, rest, old, n) == True{} : Bool}
  {mv.walk(t, rs, Up.deps.join(f, rest), old, n) == True{} : Bool}

def mv.join_miss(f, rest, t, rs, n, hn, old, e, fn, ih):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _o, _nw, _pv, _m, _sy, _tr} Up.Deps{+ds, _ss, _es, _any, _sy2, _tr2, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, old,
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, old,
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Laws.moved.ok(t, rs, old,
                M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          dn, hn, Equal.cong(String & Bool, String, p => mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Laws.moved.ok(t, rs, old,
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Laws.moved.ok(t, rs, old, M.find(ds, n)))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)),
              Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
                Laws.moved.ok(t, rs, old, M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
            String.eq(hn, n), False{}, e),
          ih))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Laws.moved.ok(t, rs, old, M.find(ds, n)))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, _bad}:
      mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)), Laws.moved.ok(t, rs, old, M.find(ds, n))),
        mv.halt_not(why))

# LAW: one step of the walk, whether or not its head is the named dependency
law mv.walk_step:
  for b: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for e: {String.eq(hn, n) == b : Bool}
  for pre: {mv.ok(Up.dep.one(U.aim(U.chosen(only,
    M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))),
    M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))), rs, only, hub,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))), t, rs,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))) == True{} : Bool}
  for ih: {mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(tl, n))),
    M.source.dep(M.find(tl, n))), rs, only, hub, M.find(tl, n)), t, rs, M.find(tl, n))
    == True{} : Bool}
    -> {mv.walk(t, rs, Up.deps.walk(rs, only, hub, tl), M.find(tl, n), n) == True{} : Bool}
  {mv.walk(t, rs, Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub,
    M.Dep{hn, hh, he, src}), Up.deps.walk(rs, only, hub, tl)),
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)), n) == True{} : Bool}

def mv.walk_step(b, t, rs, only, hub, n, hn, hh, he, src, tl, e, pre, ih):
  match b:
    case True{}:
      mv.join_hit(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), t, rs, n, hn, hh, he, src, e, pre,
        mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}))
    case False{}:
      mv.join_miss(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), t, rs, n, hn, M.find(tl, n), e,
        mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}), ih(pre))

# LAW: the walk is sound for the named dependency when its fate is
law mv.walk_ok:
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +ds: List<&2, M.Dep>
  for pre: {mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(ds, n))),
    M.source.dep(M.find(ds, n))), rs, only, hub, M.find(ds, n)), t, rs, M.find(ds, n))
    == True{} : Bool}
  {mv.walk(t, rs, Up.deps.walk(rs, only, hub, ds), M.find(ds, n), n) == True{} : Bool}

def mv.walk_ok(t, rs, only, hub, n, ds, pre):
  match ds:
    case []:
      mv.walk_nil(U.chosen(only, ""), t, rs, only, hub, n, pre)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.walk_step(String.eq(hn, n), t, rs, only, hub, n, hn, hh, he, src, tl, {==}, pre,
            p => mv.walk_ok(t, rs, only, hub, n, tl, p))

# The ledger model the upgrade renders. Every way the upgrade can end leaves
# ez.toml's model as it was, except the one where every pin was answered and
# one moved, which leaves the dependencies the walk left.

# LAW: the model, once it is known whether a pin moved
law mv.model_moved:
  for moved: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Tool>
  for wk: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(dds, n)) == True{} : Bool}
  for self: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {Laws.moved.ok(t, rs, M.find(ds, n), M.dep(Up.model.next(moved,
    M.Manifest{name, entry, bin, hub, dds, tts}, M.Manifest{name, entry, bin, hub, ds, ts}), n))
    == True{} : Bool}

def mv.model_moved(moved, _t, _rs, _n, _name, _entry, _bin, _hub, _ds, _ts, _dds, _tts, wk, self):
  match moved:
    case True{}:
      wk
    case False{}:
      self

# LAW: the model, once the sources are known
law mv.model_srcs:
  for srcs: Up.Srcs
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +ig: String
  for wk: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(dds, n)) == True{} : Bool}
  for self: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {Laws.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), n))
    == True{} : Bool}

def mv.model_srcs(srcs, t, rs, n, name, entry, bin, hub, ds, ts, dds, _ss, _es, dm, _dsy, _dtr,
  tts, tm, _tsy, _ig, wk, self):
  match srcs:
    case Up.Srcs{_fs}:
      mv.model_moved(Bool.or(dm, tm), t, rs, n, name, entry, bin, hub, ds, ts, dds, tts, wk, self)
    case Up.SrcsWait{_ask}:
      self
    case Up.SrcsNo{_why}:
      self

# LAW: the model, once `.gitignore` is known
law mv.model_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tm: Bool
  for +tsy: List<&2, String>
  for wk: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(dds, n)) == True{} : Bool}
  for self: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {Laws.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.got.ignore(said, srcs,
    M.Manifest{name, entry, bin, hub, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), n))
    == True{} : Bool}

def mv.model_ignore(said, srcs, t, rs, n, name, entry, bin, hub, ds, ts, dds, ss, es, dm, dsy, dtr,
  tts, tm, tsy, wk, self):
  match said:
    case Up.Said{+ig}:
      mv.model_srcs(srcs, t, rs, n, name, entry, bin, hub, ds, ts, dds, ss, es, dm, dsy, dtr, tts,
        tm, tsy, ig, wk, self)
    case Up.Unsaid{_why}:
      self
    case Up.Unasked{_ask}:
      self

# LAW: the model, once the pins are answered or refused
law mv.model_pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for wk: {mv.walk(t, rs, dd, M.find(ds, n), n) == True{} : Bool}
  for self: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {Laws.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.pins(dd, tt, rs,
    M.Manifest{name, entry, bin, hub, ds, ts}), n)) == True{} : Bool}

def mv.model_pins(dd, tt, t, rs, n, name, entry, bin, hub, ds, ts, wk, self):
  match dd tt:
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SCon{_c, _cs}} Up.Tools{_tts, _tm, _tsy, _tasks, _tbad}:
      self
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SCon{_c, _cs}}:
      self
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _a <> _as, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SNil{}}:
      self
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, [], SNil{}} Up.Tools{_tts, _tm, _tsy, _a <> _as, SNil{}}:
      self
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      mv.model_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), t, rs, n, name, entry,
        bin, hub, ds, ts, dds, ss, es, dm, dsy, dtr, tts, tm, tsy, wk, self)

# LAW: the model, once `--package` is known to name something
law mv.model_known:
  for k: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for wk: {mv.walk(t, rs, Up.deps.walk(rs, only, M.hub.or(hub), ds), M.find(ds, n), n)
    == True{} : Bool}
  for self: {Laws.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {Laws.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.known(k, only, rs,
    M.Manifest{name, entry, bin, hub, ds, ts}), n)) == True{} : Bool}

def mv.model_known(k, t, rs, only, n, name, entry, bin, hub, ds, ts, wk, self):
  match k:
    case False{}:
      self
    case True{}:
      mv.model_pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), t, rs,
        n, name, entry, bin, hub, ds, ts, wk, self)

# LAW: a pin by its commit alone, in any ledger an upgrade reads
law mv.fwd_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +bare: {Laws.rev_only(M.dep(r, n)) == True{} : Bool}
  {Laws.moved.ok(Up.forward(rs, M.source.url(M.source.dep(M.dep(r, n)))), rs, M.dep(r, n),
    mv.dep(Up.next(only, r, rs), n)) == True{} : Bool}

def mv.fwd_top(r, only, rs, n, bare):
  match r:
    case M.Bad{_why}:
      bare
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +ds, +ts}:
          mv.model_known(Bool.or(U.known(only, ds), M.tool.known(only, ts)),
            Up.forward(rs, M.source.url(M.source.dep(M.find(ds, n)))), rs, only, n, name, entry,
            bin, hub, ds, ts,
            mv.walk_ok(Up.forward(rs, M.source.url(M.source.dep(M.find(ds, n)))), rs, only,
              M.hub.or(hub), n, ds, mv.fwd_one(rs, only, M.hub.or(hub), M.find(ds, n), bare)),
            mv.self_dep(Up.forward(rs, M.source.url(M.source.dep(M.find(ds, n)))), rs,
              M.find(ds, n), mv.bare_git(M.find(ds, n), bare)))

# LAW: a pin through a tag, in any ledger an upgrade reads
law mv.fol_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +named: {Laws.tagged(M.dep(r, n)) == True{} : Bool}
  {Laws.moved.ok(Up.follow(rs, M.source.url(M.source.dep(M.dep(r, n))),
    M.source.tag(M.source.dep(M.dep(r, n)))), rs, M.dep(r, n),
    mv.dep(Up.next(only, r, rs), n)) == True{} : Bool}

def mv.fol_top(r, only, rs, n, named):
  match r:
    case M.Bad{_why}:
      named
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +ds, +ts}:
          mv.model_known(Bool.or(U.known(only, ds), M.tool.known(only, ts)),
            Up.follow(rs, M.source.url(M.source.dep(M.find(ds, n))),
              M.source.tag(M.source.dep(M.find(ds, n)))), rs, only, n, name, entry, bin, hub, ds, ts,
            mv.walk_ok(Up.follow(rs, M.source.url(M.source.dep(M.find(ds, n))),
              M.source.tag(M.source.dep(M.find(ds, n)))), rs, only, M.hub.or(hub), n, ds,
              mv.fol_one(rs, only, M.hub.or(hub), M.find(ds, n), named)),
            mv.self_dep(Up.follow(rs, M.source.url(M.source.dep(M.find(ds, n))),
              M.source.tag(M.source.dep(M.find(ds, n)))), rs, M.find(ds, n),
              mv.named_git(M.find(ds, n), named)))

# A plain lock leaves ez.toml's model as it is; an upgrade leaves what the
# walk decided, which is sound for the named dependency.
def Laws.upgrade_forward_moves_onward(w, n, bare):
  match w:
    case W.World{args, +ledger, _listing, _replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              mv.self_dep(Up.forward(ups, M.source.url(M.source.dep(M.dep(W.parsed(ledger), n)))),
                ups, M.dep(W.parsed(ledger), n), mv.bare_git(M.dep(W.parsed(ledger), n), bare))
            case True{}:
              mv.fwd_top(W.parsed(ledger), only, ups, n, bare)

def Laws.upgrade_tag_follows(w, n, named):
  match w:
    case W.World{args, +ledger, _listing, _replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              mv.self_dep(Up.follow(ups, M.source.url(M.source.dep(M.dep(W.parsed(ledger), n))),
                M.source.tag(M.source.dep(M.dep(W.parsed(ledger), n)))),
                ups, M.dep(W.parsed(ledger), n), mv.named_git(M.dep(W.parsed(ledger), n), named))
            case True{}:
              mv.fol_top(W.parsed(ledger), only, ups, n, named)

# The upgrade's refusals. A pin whose fate refuses makes the walk refuse,
# since a refusal ahead of the rest wins and its reason is never empty
# (`Up.halt.why`), and a walk that refuses stops the upgrade, which stops the
# lock.

# LAW: the dependency `M.find` answers from a repository has the name asked for
law mv.find_pick_named:
  for b: Bool
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for e: {String.eq(hn, n) == b : Bool}
  for g: {M.source.is_git(M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))))
    == True{} : Bool}
  for ih: {M.source.is_git(M.source.dep(M.find(tl, n))) == True{} : Bool}
    -> {M.dep.name(M.find(tl, n)) == n : String}
  {M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))) == n : String}

def mv.find_pick_named(b, n, hn, _hh, _he, _src, _tl, e, g, ih):
  match b:
    case True{}:
      Str.string_eq_true(hn, n, e)
    case False{}:
      ih(g)

law mv.find_named:
  for +ds: List<&2, M.Dep>
  for +n: String
  for g: {M.source.is_git(M.source.dep(M.find(ds, n))) == True{} : Bool}
  {M.dep.name(M.find(ds, n)) == n : String}

def mv.find_named(ds, n, g):
  match ds:
    case []:
      Eq.bit.absurd(&2, {"" == n : String}, g)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.find_pick_named(String.eq(hn, n), n, hn, hh, he, src, tl, {==}, g,
            p => mv.find_named(tl, n, p))

# LAW: and so does the one a ledger that was read answers
law mv.dep_named:
  for r: M.Read
  for +n: String
  for g: {M.source.is_git(M.source.dep(M.dep(r, n))) == True{} : Bool}
  {M.dep.name(M.dep(r, n)) == n : String}

def mv.dep_named(r, n, g):
  match r:
    case M.Bad{_why}:
      Eq.bit.absurd(&2, {"" == n : String}, g)
    case M.Good{m}:
      match m:
        case M.Manifest{_name, _entry, _bin, _hub, +ds, _ts}:
          mv.find_named(ds, n, g)

# LAW: a tip that is another commit, which the remote says does not descend
# from the pin, is refused
law mv.tip_off:
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for moved: {String.eq(rev, tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{url, rev, tip}) == Up.Asc{False{}} : Up.Asc}
  {mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend))) == True{} : Bool}

def mv.tip_off(rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br, moved, off):
  Equal.trans(Bool,
    mv.halts(Up.dep.same(String.eq(rev, tip), rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    mv.halts(Up.dep.same(False{}, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    True{},
    Equal.cong(Bool, Bool, s => mv.halts(Up.dep.same(s, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
      String.eq(rev, tip), False{}, moved),
    Equal.cong(Up.Asc, Bool, a => mv.halts(Up.dep.onward(a, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
      Up.onward(rs, Up.Above{url, rev, tip}), Up.Asc{False{}}, off))

# LAW: the pin's own commit, whose checkout no longer agrees with the pin, is
# refused
law mv.tip_drift:
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for +nar2: String
  for +root2: String
  for +man: String
  for +srcs: List<&2, String>
  for same: {String.eq(rev, tip) == True{} : Bool}
  for co: {Up.checkout(rs, Up.Tree{url, rev, he}) == Up.Co{nar2, root2, man, srcs} : Up.Co}
  for drift: {U.agree(hh, Up.hash.of(man), nar, nar2, root, root2) == False{} : Bool}
  {mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend))) == True{} : Bool}

def mv.tip_drift(rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br, nar2, root2, man,
  srcs, same, co, drift):
  Equal.trans(Bool,
    mv.halts(Up.dep.same(String.eq(rev, tip), rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    mv.halts(Up.dep.same(True{}, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    True{},
    Equal.cong(Bool, Bool, s => mv.halts(Up.dep.same(s, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
      String.eq(rev, tip), True{}, same),
    Equal.trans(Bool,
      mv.halts(Up.dep.kept(Up.checkout(rs, Up.Tree{url, rev, he}), rs, hub,
        mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg)),
      mv.halts(Up.dep.kept(Up.Co{nar2, root2, man, srcs}, rs, hub,
        mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg)),
      True{},
      Equal.cong(Up.Co, Bool, c => mv.halts(Up.dep.kept(c, rs, hub,
        mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg)),
        Up.checkout(rs, Up.Tree{url, rev, he}), Up.Co{nar2, root2, man, srcs}, co),
      Equal.cong(Bool, Bool, g => mv.halts(Up.dep.verdict(U.judge(True{}, True{}, g, tip, tg), rs,
        hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, "", Up.hash.of(man))),
        U.agree(hh, Up.hash.of(man), nar, nar2, root, root2), False{}, drift)))

# LAW: a pin by its commit alone that is asked about, whose default branch
# tip is another commit not descended from it, is refused
law mv.fwd_off_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for head: {Up.forward(rs, url) == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(rev, tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{url, rev, tip}) == Up.Asc{False{}} : Up.Asc}
  {mv.halts(Up.dep.one(U.aim(s, M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, "", root, nar, vend))) == True{} : Bool}

def mv.fwd_off_sel(s, rs, _only, hub, hn, hh, he, url, rev, root, nar, vend, tip, tg, br, sel, head,
  moved, off):
  match s:
    case False{}:
      sel
    case True{}:
      Equal.trans(Bool,
        mv.halts(Up.dep.tip(Up.forward(rs, url), rs, hub,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend))),
        mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend))),
        True{},
        Equal.cong(Up.Tip, Bool, x => mv.halts(Up.dep.tip(x, rs, hub,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend))),
          Up.forward(rs, url), Up.At{tip, tg, br}, head),
        mv.tip_off(rs, hub, hn, hh, he, url, rev, "", root, nar, vend, tip, tg, br, moved, off))

law mv.fwd_off:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for bare: {Laws.rev_only(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for head: {Up.forward(rs, M.source.url(M.source.dep(h))) == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(M.source.rev(M.source.dep(h)), tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{M.source.url(M.source.dep(h)), M.source.rev(M.source.dep(h)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h))
    == True{} : Bool}

def mv.fwd_off(rs, only, hub, h, tip, tg, br, bare, sel, head, moved, off):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}})) == True{} : Bool}, bare)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              mv.fwd_off_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, root, nar,
                vend, tip, tg, br, sel, head, moved, off)
            case SCon{+c, +ct}:
              Eq.bit.absurd(&2, {mv.halts(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))) == True{} : Bool}, bare)

# LAW: a pin through a tag that is asked about, whose tag now names another
# commit not descended from it, is refused
law mv.fol_off_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for refs: {Up.follow(rs, url, SCon{c, ct}) == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(rev, tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{url, rev, tip}) == Up.Asc{False{}} : Up.Asc}
  {mv.halts(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))) == True{} : Bool}

def mv.fol_off_sel(s, rs, _only, hub, hn, hh, he, url, rev, c, ct, root, nar, vend, tip, tg, br, sel,
  refs, moved, off):
  match s:
    case False{}:
      sel
    case True{}:
      Equal.trans(Bool,
        mv.halts(Up.dep.tip(Up.follow(rs, url, SCon{c, ct}), rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        True{},
        Equal.cong(Up.Tip, Bool, x => mv.halts(Up.dep.tip(x, rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
          Up.follow(rs, url, SCon{c, ct}), Up.At{tip, tg, br}, refs),
        mv.tip_off(rs, hub, hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend, tip, tg, br, moved,
          off))

law mv.fol_off:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for named: {Laws.tagged(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for refs: {Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h)))
    == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(M.source.rev(M.source.dep(h)), tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{M.source.url(M.source.dep(h)), M.source.rev(M.source.dep(h)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h))
    == True{} : Bool}

def mv.fol_off(rs, only, hub, h, tip, tg, br, named, sel, refs, moved, off):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}})) == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {mv.halts(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, "", root, nar, vend))) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_off_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root,
                nar, vend, tip, tg, br, sel, refs, moved, off)

# LAW: a pin through a tag that is asked about, whose tag still names its
# commit but whose checkout no longer agrees with it, is refused
law mv.fol_drift_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for +nar2: String
  for +root2: String
  for +man: String
  for +srcs: List<&2, String>
  for sel: {s == True{} : Bool}
  for refs: {Up.follow(rs, url, SCon{c, ct}) == Up.At{tip, tg, br} : Up.Tip}
  for same: {String.eq(rev, tip) == True{} : Bool}
  for co: {Up.checkout(rs, Up.Tree{url, rev, he}) == Up.Co{nar2, root2, man, srcs} : Up.Co}
  for drift: {U.agree(hh, Up.hash.of(man), nar, nar2, root, root2) == False{} : Bool}
  {mv.halts(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))) == True{} : Bool}

def mv.fol_drift_sel(s, rs, _only, hub, hn, hh, he, url, rev, c, ct, root, nar, vend, tip, tg, br,
  nar2, root2, man, srcs, sel, refs, same, co, drift):
  match s:
    case False{}:
      sel
    case True{}:
      Equal.trans(Bool,
        mv.halts(Up.dep.tip(Up.follow(rs, url, SCon{c, ct}), rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        True{},
        Equal.cong(Up.Tip, Bool, x => mv.halts(Up.dep.tip(x, rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
          Up.follow(rs, url, SCon{c, ct}), Up.At{tip, tg, br}, refs),
        mv.tip_drift(rs, hub, hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend, tip, tg, br, nar2,
          root2, man, srcs, same, co, drift))

law mv.fol_drift:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for +nar2: String
  for +root2: String
  for +man: String
  for +srcs: List<&2, String>
  for named: {Laws.tagged(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for refs: {Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h)))
    == Up.At{tip, tg, br} : Up.Tip}
  for same: {String.eq(M.source.rev(M.source.dep(h)), tip) == True{} : Bool}
  for co: {Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(h)), M.source.rev(M.source.dep(h)),
    M.dep.entry(h)}) == Up.Co{nar2, root2, man, srcs} : Up.Co}
  for drift: {U.agree(M.dep.hash(h), Up.hash.of(man), M.source.nar(M.source.dep(h)), nar2,
    M.source.root(M.source.dep(h)), root2) == False{} : Bool}
  {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h))
    == True{} : Bool}

def mv.fol_drift(rs, only, hub, h, tip, tg, br, nar2, root2, man, srcs, named, sel, refs, same, co,
  drift):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}})) == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {mv.halts(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, "", root, nar, vend))) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_drift_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root,
                nar, vend, tip, tg, br, nar2, root2, man, srcs, sel, refs, same, co, drift)

# LAW: a walk with no dependencies has no refusal to carry, so none of them
# refused
law mv.halts_nil:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for hl: {mv.halts(Up.dep.one(U.aim(s, M.Hub{}), rs, only, hub, M.Dep{"", "", "", M.Hub{}}))
    == True{} : Bool}
  {String.is_empty(mv.bad(Up.deps.walk(rs, only, hub, []))) == False{} : Bool}

def mv.halts_nil(s, _rs, _only, _hub, hl):
  match s:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hl)
    case False{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hl)

# LAW: a fate that refuses, in front of the rest, makes the walk refuse
law mv.join_bad:
  for f: Up.Fate
  for rest: Up.Deps
  for hl: {mv.halts(f) == True{} : Bool}
  {String.is_empty(mv.bad(Up.deps.join(f, rest))) == False{} : Bool}

def mv.join_bad(f, rest, hl):
  match f rest:
    case Up.Became{_d, _o, _nw, _pv, _m, _sy, _tr} Up.Deps{_ds, _ss, _es, _any, _sy2, _tr2, _asks, bad}:
      Eq.bit.absurd(&2, {String.is_empty(bad) == False{} : Bool}, hl)
    case Up.Waits{_more} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, bad}:
      Eq.bit.absurd(&2, {String.is_empty(bad) == False{} : Bool}, hl)
    case Up.Halts{why} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, _bad}:
      mv.halt_ne(why)

# LAW: and a walk that refused behind any fate still refuses
law mv.join_keeps:
  for f: Up.Fate
  for rest: Up.Deps
  for ih: {String.is_empty(mv.bad(rest)) == False{} : Bool}
  {String.is_empty(mv.bad(Up.deps.join(f, rest))) == False{} : Bool}

def mv.join_keeps(f, rest, ih):
  match f rest:
    case Up.Became{_d, _o, _nw, _pv, _m, _sy, _tr} Up.Deps{_ds, _ss, _es, _any, _sy2, _tr2, _asks, _bad}:
      ih
    case Up.Waits{_more} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, _bad}:
      ih
    case Up.Halts{why} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, _bad}:
      mv.halt_ne(why)

# LAW: one step of the walk
law mv.halts_step:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for hl: {mv.halts(Up.dep.one(U.aim(U.chosen(only,
    M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))),
    M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))), rs, only, hub,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))) == True{} : Bool}
  for ih: {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(tl, n))),
    M.source.dep(M.find(tl, n))), rs, only, hub, M.find(tl, n))) == True{} : Bool}
    -> {String.is_empty(mv.bad(Up.deps.walk(rs, only, hub, tl))) == False{} : Bool}
  {String.is_empty(mv.bad(Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub,
    M.Dep{hn, hh, he, src}), Up.deps.walk(rs, only, hub, tl)))) == False{} : Bool}

def mv.halts_step(b, rs, only, hub, _n, hn, hh, he, src, tl, hl, ih):
  match b:
    case True{}:
      mv.join_bad(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), hl)
    case False{}:
      mv.join_keeps(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), ih(hl))

# LAW: the walk refuses when the named dependency's fate does
law mv.walk_halts:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +ds: List<&2, M.Dep>
  for hl: {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(ds, n))),
    M.source.dep(M.find(ds, n))), rs, only, hub, M.find(ds, n))) == True{} : Bool}
  {String.is_empty(mv.bad(Up.deps.walk(rs, only, hub, ds))) == False{} : Bool}

def mv.walk_halts(rs, only, hub, n, ds, hl):
  match ds:
    case []:
      mv.halts_nil(U.chosen(only, ""), rs, only, hub, hl)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.halts_step(String.eq(hn, n), rs, only, hub, n, hn, hh, he, src, tl, hl,
            p => mv.walk_halts(rs, only, hub, n, tl, p))

# LAW: a walk that refuses stops the upgrade
law mv.pins_stop:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for wb: {String.is_empty(mv.bad(dd)) == False{} : Bool}
  {mv.stops(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds, ts})) == True{} : Bool}

def mv.pins_stop(dd, tt, rs, name, entry, bin, hub, ds, ts, wb):
  match dd tt:
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, +dasks, SNil{}} Up.Tools{+tts, +tm, +tsy, +tasks, +tbad}:
      Eq.bit.absurd2(&2, {mv.stops(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, ""},
        Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, ds, ts}))
        == True{} : Bool}, wb)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SCon{_c, _cs}} Up.Tools{_tts, _tm, _tsy, _tasks, _tbad}:
      {==}

# LAW: and so does a `--package` that names nothing
law mv.known_stop:
  for k: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for wb: {String.is_empty(mv.bad(Up.deps.walk(rs, only, M.hub.or(hub), ds))) == False{} : Bool}
  {mv.stops(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds, ts})) == True{} : Bool}

def mv.known_stop(k, rs, only, name, entry, bin, hub, ds, ts, wb):
  match k:
    case False{}:
      {==}
    case True{}:
      mv.pins_stop(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), rs, name,
        entry, bin, hub, ds, ts, wb)

# LAW: an upgrade that stops is a lock that refuses
law mv.refuses_of:
  for nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for st: {mv.stops(nx) == True{} : Bool}
  {P.refuses.doc(P.decide(W.inputs.of(nx, listing, replies))) == True{} : Bool}

def mv.refuses_of(nx, listing, replies, st):
  match nx:
    case Up.Next{+model, +read, SNil{}, +asks, +trees, +vends, +says, +edits, +found, +drops, +swaps}:
      Eq.bit.absurd(&2, {P.refuses.doc(P.decide(W.inputs.of(Up.Next{model, read, "", asks, trees,
        vends, says, edits, found, drops, swaps}, listing, replies))) == True{} : Bool}, st)
    case Up.Next{_model, _read, SCon{_c, _cs}, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps}:
      {==}

# LAW: a lock refuses when the named dependency's fate under `--upgrade` does
law mv.refuses_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +n: String
  for g: {M.source.is_git(M.source.dep(M.dep(r, n))) == True{} : Bool}
  for hl: {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.dep(r, n))),
    M.source.dep(M.dep(r, n))), rs, only, M.hub_of(r), M.dep(r, n))) == True{} : Bool}
  {P.refuses.doc(P.decide(W.inputs.of(Up.next(only, r, rs), listing, replies))) == True{} : Bool}

def mv.refuses_top(r, only, rs, listing, replies, n, g, hl):
  match r:
    case M.Bad{+why}:
      Eq.bit.absurd(&2, {P.refuses.doc(P.decide(W.inputs.of(Up.next(only, M.Bad{why}, rs), listing,
        replies))) == True{} : Bool}, g)
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +ds, +ts}:
          mv.refuses_of(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, ds, ts}}, rs), listing,
            replies, mv.known_stop(Bool.or(U.known(only, ds), M.tool.known(only, ts)), rs, only,
              name, entry, bin, hub, ds, ts, mv.walk_halts(rs, only, M.hub.or(hub), n, ds, hl)))

# `--package` names the dependency, so it is the one asked about
def Laws.upgrade_forward_refuses_off(w, n, tip, tag, branch, up, bare, sel, head, moved, off):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {P.refuses(W.World{W.Args{False{}, only}, ledger, listing, replies,
                ups}) == True{} : Bool}, up)
            case True{}:
              mv.refuses_top(W.parsed(ledger), only, ups, listing, replies, n,
                mv.bare_git(M.dep(W.parsed(ledger), n), bare),
                mv.fwd_off(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                  tag, branch, bare,
                  Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                    U.chosen(only, n), True{},
                    Equal.cong(String, Bool, x => U.chosen(only, x),
                      M.dep.name(M.dep(W.parsed(ledger), n)), n,
                      mv.dep_named(W.parsed(ledger), n, mv.bare_git(M.dep(W.parsed(ledger), n), bare))),
                    sel),
                  head, moved, off))

def Laws.upgrade_tag_refuses_off(w, n, tip, tag, branch, up, named, sel, refs, moved, off):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {P.refuses(W.World{W.Args{False{}, only}, ledger, listing, replies,
                ups}) == True{} : Bool}, up)
            case True{}:
              mv.refuses_top(W.parsed(ledger), only, ups, listing, replies, n,
                mv.named_git(M.dep(W.parsed(ledger), n), named),
                mv.fol_off(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                  tag, branch, named,
                  Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                    U.chosen(only, n), True{},
                    Equal.cong(String, Bool, x => U.chosen(only, x),
                      M.dep.name(M.dep(W.parsed(ledger), n)), n,
                      mv.dep_named(W.parsed(ledger), n, mv.named_git(M.dep(W.parsed(ledger), n), named))),
                    sel),
                  refs, moved, off))

def Laws.upgrade_tag_refuses_drift(w, n, tip, tag, branch, nar, root, manifest, srcs, up, named, sel,
  refs, same, co, drift):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {P.refuses(W.World{W.Args{False{}, only}, ledger, listing, replies,
                ups}) == True{} : Bool}, up)
            case True{}:
              mv.refuses_top(W.parsed(ledger), only, ups, listing, replies, n,
                mv.named_git(M.dep(W.parsed(ledger), n), named),
                mv.fol_drift(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                  tag, branch, nar, root, manifest, srcs, named,
                  Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                    U.chosen(only, n), True{},
                    Equal.cong(String, Bool, x => U.chosen(only, x),
                      M.dep.name(M.dep(W.parsed(ledger), n)), n,
                      mv.dep_named(W.parsed(ledger), n, mv.named_git(M.dep(W.parsed(ledger), n), named))),
                    sel),
                  refs, same, co, drift))

# The upgrade reaches the tip. When the lock does not refuse, every pin it
# asked about is at the commit the remote named: moved there, which marks the
# upgrade as having moved a pin, so the ledger it writes is the walk's; or
# there already.

# a fate reaches `tip`: the pin it leaves is at it, and either the fate
# moved it or the old pin was at it already
def mv.live(fate: Up.Fate, +tip: String, +old: M.Dep) -> Bool:
  match fate:
    case Up.Became{d, _o, _n, _p, m, _s, _t}:
      Bool.and(String.eq(M.source.rev(M.source.dep(d)), tip),
        Bool.or(m, String.eq(M.source.rev(M.source.dep(old)), tip)))
    case Up.Waits{_asks}:
      True{}
    case Up.Halts{_why}:
      True{}

# the walk reaches `tip` for the dependency named `n`: it refuses, or still
# asks, or the dependency it leaves under that name is at `tip`, and either a
# pin moved or the old pin was at `tip` already
def mv.walk_live(+tip: String, dd: Up.Deps, +old: M.Dep, +n: String) -> Bool:
  Up.Deps{ds, _ss, _es, m, _sy, _tr, asks, bad} = dd
  Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
    Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
      Bool.or(m, String.eq(M.source.rev(M.source.dep(old)), tip)))))

# LAW: a fate that reaches the tip, in front of the rest, still does
law mv.live_or:
  for x: Bool
  for m: Bool
  for +any: Bool
  for +c: Bool
  for lv: {Bool.and(x, Bool.or(m, c)) == True{} : Bool}
  {Bool.and(x, Bool.or(Bool.or(m, any), c)) == True{} : Bool}

def mv.live_or(x, m, any, c, lv):
  match x m:
    case False{} _:
      lv
    case True{} True{}:
      {==}
    case True{} False{}:
      mv.or_r(any, c, lv)

# LAW: and one behind another pin that moved or not
law mv.live_keep:
  for a: Bool
  for b: Bool
  for x: Bool
  for m: Bool
  for +any: Bool
  for +c: Bool
  for ih: {Bool.or(a, Bool.or(b, Bool.and(x, Bool.or(any, c)))) == True{} : Bool}
  {Bool.or(a, Bool.or(b, Bool.and(x, Bool.or(Bool.or(m, any), c)))) == True{} : Bool}

def mv.live_keep(a, b, x, m, _any, _c, ih):
  match a b x m:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} False{} _:
      ih
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      ih

# LAW: a pin moved to the tip, once the hub has not objected
law mv.live_hub:
  for hb: Up.Hubbed
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +hash: String
  for +tip: String
  for +br: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  {mv.live(Up.dep.hub(hb, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), hash, tip, root2,
    nar2, man, srcs, br), tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_hub(hb, _hn, _hh, _he, _url, _rev, _tag, _root, _nar, _vend, _hash, tip, _br, _root2,
  _nar2, _man, _srcs):
  match hb:
    case Up.Clear{}:
      Equal.cong(Bool, Bool, x => Bool.and(x, True{}), String.eq(tip, tip), True{},
        Eq.string_eq_self(tip))
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved to the tip, once its checkout is in
law mv.live_adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +br: String
  {mv.live(Up.dep.advance(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, br),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_adv(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, br):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      mv.live_hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), hn, hh, he, url, rev, tag, root,
        nar, vend, Up.hash.of(man), tip, br, root2, nar2, man, srcs)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: a tip that is another commit, once ancestry is in
law mv.live_onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  {mv.live(Up.dep.onward(a, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_onward(a, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, _tg, br):
  match a:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          mv.live_adv(Up.checkout(rs, Up.Tree{url, tip, he}), rs, hub, hn, hh, he, url, rev, tag,
            root, nar, vend, tip, br)
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the pin's own commit, kept when its checkout agrees
law mv.live_agree:
  for g: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +seen: String
  for e: {String.eq(rev, tip) == True{} : Bool}
  {mv.live(Up.dep.verdict(U.judge(True{}, True{}, g, tip, tg), rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, "", seen),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_agree(g, _rs, _hub, _hn, _hh, _he, _url, rev, _tag, _root, _nar, _vend, tip, _tg,
  _seen, e):
  match g:
    case True{}:
      Equal.cong(Bool, Bool, x => Bool.and(x, x), String.eq(rev, tip), True{}, e)
    case False{}:
      {==}

# LAW: the pin's own commit, once its checkout is in
law mv.live_kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for e: {String.eq(rev, tip) == True{} : Bool}
  {mv.live(Up.dep.kept(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_kept(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, e):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      mv.live_agree(U.agree(hh, Up.hash.of(man), nar, nar2, root, root2), rs, hub, hn, hh, he, url,
        rev, tag, root, nar, vend, tip, tg, Up.hash.of(man), e)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: the tip against the pin
law mv.live_same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for e: {String.eq(rev, tip) == s : Bool}
  {mv.live(Up.dep.same(s, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_same(s, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br, e):
  match s:
    case True{}:
      mv.live_kept(Up.checkout(rs, Up.Tree{url, rev, he}), rs, hub, hn, hh, he, url, rev, tag, root,
        nar, vend, tip, tg, e)
    case False{}:
      mv.live_onward(Up.onward(rs, Up.Above{url, rev, tip}), rs, hub, hn, hh, he, url, rev, tag,
        root, nar, vend, tip, tg, br)

# LAW: a pin reaches the tip the remote named
law mv.live_tip:
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  {mv.live(Up.dep.tip(Up.At{tip, tg, br}, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_tip(rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br):
  mv.live_same(String.eq(rev, tip), rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg,
    br, {==})

# LAW: a pin by its commit alone that is asked about reaches its default
# branch tip
law mv.fwd_live_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for head: {Up.forward(rs, url) == Up.At{tip, tg, br} : Up.Tip}
  {mv.live(Up.dep.one(U.aim(s, M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
    mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}

def mv.fwd_live_sel(s, rs, only, hub, hn, hh, he, url, rev, root, nar, vend, tip, tg, br, sel, head):
  match s:
    case False{}:
      Eq.bit.absurd(&2, {mv.live(Up.dep.one(U.aim(False{}, M.Git{url, rev, "", root, nar, vend}), rs,
        only, hub, mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
        mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}, sel)
    case True{}:
      Equal.trans(Bool,
        mv.live(Up.dep.tip(Up.forward(rs, url), rs, hub,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend)),
        mv.live(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend)),
        True{},
        Equal.cong(Up.Tip, Bool, x => mv.live(Up.dep.tip(x, rs, hub,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
          mv.git(hn, hh, he, url, rev, "", root, nar, vend)),
          Up.forward(rs, url), Up.At{tip, tg, br}, head),
        mv.live_tip(rs, hub, hn, hh, he, url, rev, "", root, nar, vend, tip, tg, br))

law mv.fwd_live:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for bare: {Laws.rev_only(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for head: {Up.forward(rs, M.source.url(M.source.dep(h))) == Up.At{tip, tg, br} : Up.Tip}
  {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    tip, h) == True{} : Bool}

def mv.fwd_live(rs, only, hub, h, tip, tg, br, bare, sel, head):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.live(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}}), tip, M.Dep{hn, hh, he, M.Hub{}}) == True{} : Bool}, bare)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              mv.fwd_live_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, root, nar,
                vend, tip, tg, br, sel, head)
            case SCon{+c, +ct}:
              Eq.bit.absurd(&2, {mv.live(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
                mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}, bare)

# LAW: a pin through a tag that is asked about reaches what its tag names
law mv.fol_live_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for refs: {Up.follow(rs, url, SCon{c, ct}) == Up.At{tip, tg, br} : Up.Tip}
  {mv.live(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
    mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}

def mv.fol_live_sel(s, rs, only, hub, hn, hh, he, url, rev, c, ct, root, nar, vend, tip, tg, br, sel,
  refs):
  match s:
    case False{}:
      Eq.bit.absurd(&2, {mv.live(Up.dep.one(U.aim(False{}, M.Git{url, rev, SCon{c, ct}, root, nar,
        vend}), rs, only, hub, mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
        mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}, sel)
    case True{}:
      Equal.trans(Bool,
        mv.live(Up.dep.tip(Up.follow(rs, url, SCon{c, ct}), rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)),
        mv.live(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)),
        True{},
        Equal.cong(Up.Tip, Bool, x => mv.live(Up.dep.tip(x, rs, hub,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
          mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)),
          Up.follow(rs, url, SCon{c, ct}), Up.At{tip, tg, br}, refs),
        mv.live_tip(rs, hub, hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend, tip, tg, br))

law mv.fol_live:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for named: {Laws.tagged(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for refs: {Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h)))
    == Up.At{tip, tg, br} : Up.Tip}
  {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    tip, h) == True{} : Bool}

def mv.fol_live(rs, only, hub, h, tip, tg, br, named, sel, refs):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          Eq.bit.absurd(&2, {mv.live(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{}}), tip, M.Dep{hn, hh, he, M.Hub{}}) == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {mv.live(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
                mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_live_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root,
                nar, vend, tip, tg, br, sel, refs)

# LAW: a walk over no dependencies reaches the tip exactly when the blank pin
# does
law mv.live_nil:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +tip: String
  for lv: {mv.live(Up.dep.one(U.aim(s, M.Hub{}), rs, only, hub, M.Dep{"", "", "", M.Hub{}}), tip,
    M.Dep{"", "", "", M.Hub{}}) == True{} : Bool}
  {mv.walk_live(tip, Up.deps.walk(rs, only, hub, []), M.Dep{"", "", "", M.Hub{}}, n) == True{} : Bool}

def mv.live_nil(s, _rs, _only, _hub, _n, _tip, lv):
  match s:
    case True{}:
      lv
    case False{}:
      lv

# LAW: the named dependency's fate in front of the rest
law mv.live_hit:
  for f: Up.Fate
  for rest: Up.Deps
  for +n: String
  for +tip: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for e: {String.eq(hn, n) == True{} : Bool}
  for lv: {mv.live(f, tip, M.Dep{hn, hh, he, src}) == True{} : Bool}
  for fn: {mv.fine(f, hn) == (hn, True{}) : String & Bool}
  {mv.walk_live(tip, Up.deps.join(f, rest), M.Dep{hn, hh, he, src}, n) == True{} : Bool}

def mv.live_hit(f, rest, n, tip, hn, hh, he, src, e, lv, fn):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _o, _nw, _pv, +m, _sy, _tr} Up.Deps{+ds, _ss, _es, +any, _sy2, _tr2, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
          dn, hn, Equal.cong(String & Bool, String, p => mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(dsrc), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(M.source.dep(
                M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
            String.eq(hn, n), True{}, e),
          mv.or_r(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(dsrc), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip)))),
            mv.or_r(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(dsrc), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))),
              mv.live_or(String.eq(M.source.rev(dsrc), tip), m, any,
                String.eq(M.source.rev(src), tip), lv)))))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(src), tip))))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, _bad}:
      mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(src), tip)))),
        mv.halt_not(why))

# LAW: another dependency's fate in front of the rest
law mv.live_miss:
  for f: Up.Fate
  for rest: Up.Deps
  for +n: String
  for +tip: String
  for +hn: String
  for +old: M.Dep
  for e: {String.eq(hn, n) == False{} : Bool}
  for fn: {mv.fine(f, hn) == (hn, True{}) : String & Bool}
  for ih: {mv.walk_live(tip, rest, old, n) == True{} : Bool}
  {mv.walk_live(tip, Up.deps.join(f, rest), old, n) == True{} : Bool}

def mv.live_miss(f, rest, n, tip, hn, old, e, fn, ih):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _o, _nw, _pv, +m, _sy, _tr} Up.Deps{+ds, _ss, _es, +any, _sy2, _tr2, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
          dn, hn, Equal.cong(String & Bool, String, p => mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(M.source.dep(
                M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
            String.eq(hn, n), False{}, e),
          mv.live_keep(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks)),
            String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip), m, any,
            String.eq(M.source.rev(M.source.dep(old)), tip), ih)))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(M.source.dep(old)), tip))))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, _bad}:
      mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(M.source.dep(old)), tip)))),
        mv.halt_not(why))

# LAW: one step of the walk
law mv.live_step:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +tip: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for e: {String.eq(hn, n) == b : Bool}
  for lv: {mv.live(Up.dep.one(U.aim(U.chosen(only,
    M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))),
    M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))), rs, only, hub,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))), tip,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))) == True{} : Bool}
  for ih: {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(tl, n))),
    M.source.dep(M.find(tl, n))), rs, only, hub, M.find(tl, n)), tip, M.find(tl, n))
    == True{} : Bool}
    -> {mv.walk_live(tip, Up.deps.walk(rs, only, hub, tl), M.find(tl, n), n) == True{} : Bool}
  {mv.walk_live(tip, Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub,
    M.Dep{hn, hh, he, src}), Up.deps.walk(rs, only, hub, tl)),
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)), n) == True{} : Bool}

def mv.live_step(b, rs, only, hub, n, tip, hn, hh, he, src, tl, e, lv, ih):
  match b:
    case True{}:
      mv.live_hit(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), n, tip, hn, hh, he, src, e, lv,
        mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}))
    case False{}:
      mv.live_miss(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), n, tip, hn, M.find(tl, n), e,
        mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}), ih(lv))

# LAW: the walk reaches the tip when the named dependency's fate does
law mv.walk_reaches:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +tip: String
  for +ds: List<&2, M.Dep>
  for lv: {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(ds, n))),
    M.source.dep(M.find(ds, n))), rs, only, hub, M.find(ds, n)), tip, M.find(ds, n))
    == True{} : Bool}
  {mv.walk_live(tip, Up.deps.walk(rs, only, hub, ds), M.find(ds, n), n) == True{} : Bool}

def mv.walk_reaches(rs, only, hub, n, tip, ds, lv):
  match ds:
    case []:
      mv.live_nil(U.chosen(only, ""), rs, only, hub, n, tip, lv)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.live_step(String.eq(hn, n), rs, only, hub, n, tip, hn, hh, he, src, tl, {==}, lv,
            p => mv.walk_reaches(rs, only, hub, n, tip, tl, p))

# LAW: a reason that is refused is not empty, so an upgrade that stops with
# it is not one whose stop is empty
law mv.halt_clash:
  for why: String
  for se: {String.is_empty(Up.halt.why(why)) == True{} : Bool}
  {False{} == True{} : Bool}

def mv.halt_clash(why, se):
  Equal.trans(Bool, False{}, String.is_empty(Up.halt.why(why)), True{},
    Equal.sym(Bool, String.is_empty(Up.halt.why(why)), False{}, mv.halt_ne(why)), se)

# LAW: the model, once it is known whether any pin moved
law mv.reach_moved:
  for dm: Bool
  for tm: Bool
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Tool>
  for wk: {Bool.and(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
    Bool.or(dm, String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(M.dep(Up.model.next(Bool.or(dm, tm),
    M.Manifest{name, entry, bin, hub, dds, tts}, M.Manifest{name, entry, bin, hub, ds, ts}), n))),
    tip) == True{} : Bool}

def mv.reach_moved(dm, tm, tip, n, _name, _entry, _bin, _hub, ds, _ts, dds, _tts, wk):
  match dm tm:
    case True{} _:
      Eq.and.left(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip), True{}, wk)
    case False{} True{}:
      Eq.and.left(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
        String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip), wk)
    case False{} False{}:
      Eq.and.right(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
        String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip), wk)

# LAW: the model, once the sources are known
law mv.reach_srcs:
  for srcs: Up.Srcs
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +ig: String
  for wk: {Bool.and(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
    Bool.or(dm, String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip))) == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), n))), tip)
    == True{} : Bool}

def mv.reach_srcs(srcs, tip, n, name, entry, bin, hub, ds, ts, dds, _ss, _es, dm, _dsy, _dtr, tts,
  tm, _tsy, _ig, wk, se):
  match srcs:
    case Up.Srcs{_fs}:
      mv.reach_moved(dm, tm, tip, n, name, entry, bin, hub, ds, ts, dds, tts, wk)
    case Up.SrcsWait{_ask}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        se)
    case Up.SrcsNo{+why}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        mv.halt_clash(why, se))

# LAW: the model, once `.gitignore` is known
law mv.reach_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tm: Bool
  for +tsy: List<&2, String>
  for wk: {Bool.and(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
    Bool.or(dm, String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip))) == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs,
    M.Manifest{name, entry, bin, hub, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.got.ignore(said, srcs,
    M.Manifest{name, entry, bin, hub, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), n))), tip)
    == True{} : Bool}

def mv.reach_ignore(said, srcs, tip, n, name, entry, bin, hub, ds, ts, dds, ss, es, dm, dsy, dtr, tts,
  tm, tsy, wk, se):
  match said:
    case Up.Said{+ig}:
      mv.reach_srcs(srcs, tip, n, name, entry, bin, hub, ds, ts, dds, ss, es, dm, dsy, dtr, tts, tm,
        tsy, ig, wk, se)
    case Up.Unsaid{+why}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        mv.halt_clash(why, se))
    case Up.Unasked{_ask}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        se)

# LAW: the model, once the pins are answered or refused
law mv.reach_pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for wk: {mv.walk_live(tip, dd, M.find(ds, n), n) == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds, ts})))
    == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.pins(dd, tt, rs,
    M.Manifest{name, entry, bin, hub, ds, ts}), n))), tip) == True{} : Bool}

def mv.reach_pins(dd, tt, rs, tip, n, name, entry, bin, hub, ds, ts, wk, se):
  match dd tt:
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SCon{_c, _cs}} Up.Tools{_tts, _tm, _tsy, _tasks, _tbad}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SCon{_c, _cs}}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _a <> _as, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SNil{}}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, [], SNil{}} Up.Tools{_tts, _tm, _tsy, _a <> _as, SNil{}}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      mv.reach_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), tip, n, name, entry,
        bin, hub, ds, ts, dds, ss, es, dm, dsy, dtr, tts, tm, tsy, wk, se)

# LAW: the model, once `--package` is known to name something
law mv.reach_known:
  for k: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for wk: {mv.walk_live(tip, Up.deps.walk(rs, only, M.hub.or(hub), ds), M.find(ds, n), n)
    == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds, ts})))
    == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.known(k, only, rs,
    M.Manifest{name, entry, bin, hub, ds, ts}), n))), tip) == True{} : Bool}

def mv.reach_known(k, rs, only, tip, n, name, entry, bin, hub, ds, ts, wk, se):
  match k:
    case False{}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case True{}:
      mv.reach_pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), rs, tip,
        n, name, entry, bin, hub, ds, ts, wk, se)

# LAW: a lock that does not refuse has an upgrade that did not stop
law mv.stop_empty:
  for nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for ok: {P.refuses.doc(P.decide(W.inputs.of(nx, listing, replies))) == False{} : Bool}
  {String.is_empty(Up.next.stop(nx)) == True{} : Bool}

def mv.stop_empty(nx, _listing, _replies, ok):
  match nx:
    case Up.Next{_model, _read, SNil{}, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps}:
      {==}
    case Up.Next{_model, _read, SCon{_c, _cs}, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, ok)

# LAW: in any ledger an upgrade reads, a pin whose fate reaches the tip is at
# it in the model, when the upgrade does not stop
law mv.reach_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +tip: String
  for g: {M.source.is_git(M.source.dep(M.dep(r, n))) == True{} : Bool}
  for lv: {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.dep(r, n))),
    M.source.dep(M.dep(r, n))), rs, only, M.hub_of(r), M.dep(r, n)), tip, M.dep(r, n))
    == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.next(only, r, rs), n))), tip) == True{} : Bool}

def mv.reach_top(r, only, rs, n, tip, g, lv, se):
  match r:
    case M.Bad{+why}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(mv.dep(Up.next(only, M.Bad{why}, rs), n))),
        tip) == True{} : Bool}, g)
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +ds, +ts}:
          mv.reach_known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), rs, only, tip, n, name,
            entry, bin, hub, ds, ts, mv.walk_reaches(rs, only, M.hub.or(hub), n, tip, ds, lv), se)

def Laws.upgrade_forward_reaches_tip(w, n, tip, tag, branch, up, bare, sel, head, ok):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {M.source.rev(M.source.dep(M.dep(P.ledger.next(W.World{
                W.Args{False{}, only}, ledger, listing, replies, ups}), n))) == tip : String}, up)
            case True{}:
              Str.string_eq_true(M.source.rev(M.source.dep(mv.dep(Up.next(only, W.parsed(ledger), ups),
                n))), tip,
                mv.reach_top(W.parsed(ledger), only, ups, n, tip,
                  mv.bare_git(M.dep(W.parsed(ledger), n), bare),
                  mv.fwd_live(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                    tag, branch, bare,
                    Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                      U.chosen(only, n), True{},
                      Equal.cong(String, Bool, x => U.chosen(only, x),
                        M.dep.name(M.dep(W.parsed(ledger), n)), n,
                        mv.dep_named(W.parsed(ledger), n, mv.bare_git(M.dep(W.parsed(ledger), n), bare))),
                      sel),
                    head),
                  mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok)))

def Laws.upgrade_tag_resolves(w, n, tip, tag, branch, up, named, sel, refs, ok):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {M.source.rev(M.source.dep(M.dep(P.ledger.next(W.World{
                W.Args{False{}, only}, ledger, listing, replies, ups}), n))) == tip : String}, up)
            case True{}:
              Str.string_eq_true(M.source.rev(M.source.dep(mv.dep(Up.next(only, W.parsed(ledger), ups),
                n))), tip,
                mv.reach_top(W.parsed(ledger), only, ups, n, tip,
                  mv.named_git(M.dep(W.parsed(ledger), n), named),
                  mv.fol_live(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                    tag, branch, named,
                    Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                      U.chosen(only, n), True{},
                      Equal.cong(String, Bool, x => U.chosen(only, x),
                        M.dep.name(M.dep(W.parsed(ledger), n)), n,
                        mv.dep_named(W.parsed(ledger), n, mv.named_git(M.dep(W.parsed(ledger), n), named))),
                      sel),
                    refs),
                  mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok)))
