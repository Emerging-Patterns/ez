# lock: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import ./up.bend as Up
import ../manifest/manifest.bend as M
import ../manifest/upgrade.bend as U
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

# The upgrade's decisions: what it keeps (EZ-RES-4, EZ-RES-6) and what it
# asks (EZ-RES-6). The upgrade walks the ledger's dependencies and tools one
# at a time, each by what `U.aim` makes of it, so every law is a lemma about
# one entry's fate, an induction over the list, and a pass through the
# pipeline `Up.next` runs the two walks through, which leaves the ledger
# model either as it was or with the walked lists in place of the old ones.

# LAW: string equality reads the same either way round
law eq_sym:
  for +a: String
  for +b: String
  {String.eq(a, b) == String.eq(b, a) : Bool}

# LAW: with the first answer given
law eq_sym.go:
  for c: Bool
  for +a: String
  for +b: String
  for +e: {String.eq(a, b) == c : Bool}
  {c == String.eq(b, a) : Bool}

# LAW: and a second that cannot be True when the first was False
law eq_sym.no:
  for d: Bool
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == False{} : Bool}
  for f: {String.eq(b, a) == d : Bool}
  {False{} == d : Bool}

def eq_sym.no(d, a, b, e, f):
  match d:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool},
        Equal.trans(Bool, True{}, String.eq(a, b), False{},
          Equal.trans(Bool, True{}, String.eq(a, a), String.eq(a, b),
            Equal.sym(Bool, String.eq(a, a), True{}, Eq.string_eq_self(a)),
            Equal.cong(String, Bool, x => String.eq(a, x), a, b,
              Equal.sym(String, b, a, Str.string_eq_true(b, a, f)))),
          e))

def eq_sym.go(c, a, b, e):
  match c:
    case True{}:
      ab = Str.string_eq_true(a, b, e)
      %ab : {True{} == String.eq(_, a) : Bool}
      Equal.sym(Bool, String.eq(a, a), True{}, Eq.string_eq_self(a))
    case False{}:
      eq_sym.no(String.eq(b, a), a, b, e, {==})

def eq_sym(a, b):
  eq_sym.go(String.eq(a, b), a, b, {==})

# LAW: a nonempty `--package n` does not choose a name `n` is not
law unchosen:
  for +n: String
  for +m: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {U.chosen(n, m) == False{} : Bool}

def unchosen(n, m, ne, d):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {U.chosen.go(_, n, m) == False{} : Bool}
  d

# LAW: and whether it chooses a name is the name read against it
law chosen_named:
  for +n: String
  for +x: String
  for ne: {String.is_empty(n) == False{} : Bool}
  {U.chosen(n, x) == String.eq(x, n) : Bool}

def chosen_named(n, x, ne):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {U.chosen.go(_, n, x) == String.eq(x, n) : Bool}
  eq_sym(n, x)

# LAW: an entry that is not chosen is held
law unchosen_holds:
  for +n: String
  for +m: String
  for s: M.Source
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {U.aim(U.chosen(n, m), s) == U.Hold{} : U.Aim}

def unchosen_holds(n, m, s, ne, d):
  us = Equal.sym(Bool, U.chosen(n, m), False{}, unchosen(n, m, ne, d))
  %us : {U.aim(_, s) == U.Hold{} : U.Aim}
  {==}

# LAW: and a hub entry is held whether it is chosen or not
law hub_holds:
  for sel: Bool
  for s: M.Source
  for e: {M.source.is_git(s) == False{} : Bool}
  {U.aim(sel, s) == U.Hold{} : U.Aim}

# LAW: a hub source is held, chosen or not
law hub_source_holds:
  for sel: Bool
  {U.aim(sel, M.Hub{}) == U.Hold{} : U.Aim}

def hub_source_holds(sel):
  match sel:
    case True{}:
      {==}
    case False{}:
      {==}

def hub_holds(sel, s, e):
  match s:
    case M.Hub{}:
      hub_source_holds(sel)
    case M.Git{url, rev, tag, root, nar, vend}:
      Eq.bit.absurd2(&2, {U.aim(sel, M.Git{url, rev, tag, root, nar, vend}) == U.Hold{} : U.Aim}, e)

# One dependency's fate keeps its name. Law vocabulary for the walk below.

# the name a fate leaves in the ledger, or `x` when it leaves none
def fate.name(f: Up.Fate, x: String) -> String:
  match f:
    case Up.Became{d, _old, _new, _prev, _moved, _says, _trees}:
      M.dep.name(d)
    case Up.Waits{_asks}:
      x
    case Up.Halts{_why}:
      x

# LAW: a dependency retargeted keeps its name
law retarget_name:
  for dep: M.Dep
  for rev: String
  for hash: String
  for root: String
  for nar: String
  {M.dep.name(U.retarget(dep, rev, hash, root, nar)) == M.dep.name(dep) : String}

def retarget_name(dep, _rev, _hash, _root, _nar):
  match dep:
    case M.Dep{n, h, e, s}:
      match s:
        case M.Hub{}:
          {==}
        case M.Git{url, r, tag, rt, nr, vend}:
          {==}

law moved_name:
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {fate.name(Up.dep.moved(dep, hash, rev, root, nar, manifest, srcs, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def moved_name(dep, hash, rev, root, nar, _manifest, _srcs, _branch):
  retarget_name(dep, rev, hash, root, nar)

law hub_name:
  for hubbed: Up.Hubbed
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {fate.name(Up.dep.hub(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def hub_name(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch):
  match hubbed:
    case Up.Clear{}:
      moved_name(dep, hash, rev, root, nar, manifest, srcs, branch)
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

law advance_name:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +rev: String
  for +branch: String
  {fate.name(Up.dep.advance(co, rs, hub, dep, rev, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def advance_name(co, rs, hub, dep, rev, branch):
  match co:
    case Up.Co{nar, root, +manifest, srcs}:
      hub_name(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(manifest)}), dep, Up.hash.of(manifest),
        rev, root, nar, manifest, srcs, branch)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law verdict_name:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +branch: String
  for +seen: String
  {fate.name(Up.dep.verdict(verdict, rs, hub, dep, tip, branch, seen), M.dep.name(dep))
    == M.dep.name(dep) : String}

def verdict_name(verdict, rs, hub, dep, _tip, branch, _seen):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      advance_name(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)), rev, M.dep.entry(dep)}),
        rs, hub, dep, rev, branch)

law kept_name:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  {fate.name(Up.dep.kept(co, rs, hub, dep, tip, tag), M.dep.name(dep))
    == M.dep.name(dep) : String}

def kept_name(co, rs, hub, dep, tip, tag):
  match co:
    case Up.Co{nar, root, +manifest, _srcs}:
      verdict_name(U.judge(True{}, True{},
        U.agree(M.dep.hash(dep), Up.hash.of(manifest), M.source.nar(M.source.dep(dep)), nar,
          M.source.root(M.source.dep(dep)), root), tip, tag), rs, hub, dep, tip, "",
        Up.hash.of(manifest))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law onward_name:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {fate.name(Up.dep.onward(asc, rs, hub, dep, tip, tag, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def onward_name(asc, rs, hub, dep, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      verdict_name(U.judge(False{}, yes, False{}, tip, tag), rs, hub, dep, tip, branch, "")
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law same_name:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {fate.name(Up.dep.same(same, rs, hub, dep, tip, tag, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def same_name(same, rs, hub, dep, tip, tag, branch):
  match same:
    case True{}:
      kept_name(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), M.dep.entry(dep)}), rs, hub, dep, tip, tag)
    case False{}:
      onward_name(Up.onward(rs, Up.Above{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), tip}), rs, hub, dep, tip, tag, branch)

law tip_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  {fate.name(Up.dep.tip(tip, rs, hub, dep), M.dep.name(dep)) == M.dep.name(dep) : String}

def tip_name(tip, rs, hub, dep):
  match tip:
    case Up.At{+rev, tag, branch}:
      same_name(String.eq(M.source.rev(M.source.dep(dep)), rev), rs, hub, dep, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: whatever the upgrade makes of one dependency, what it leaves in the
# ledger has the dependency's name
law one_name:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +dep: M.Dep
  {fate.name(Up.dep.one(aim, rs, only, hub, dep), M.dep.name(dep)) == M.dep.name(dep) : String}

def one_name(aim, rs, _only, hub, dep):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      tip_name(Up.follow(rs, M.source.url(M.source.dep(dep)), ref), rs, hub, dep)
    case U.Forward{}:
      tip_name(Up.forward(rs, M.source.url(M.source.dep(dep))), rs, hub, dep)

# the dependencies a walk leaves
def deps.of(dd: Up.Deps) -> List<&2, M.Dep>:
  Up.Deps{ds, _ss, _es, _m, _sy, _tr, _asks, _bad} = dd
  ds

# LAW: an entry of another name, joined in front of the rest, is passed over
# by a lookup
law join_skip:
  for f: Up.Fate
  for r: Up.Deps
  for +x: String
  for +m: String
  for nf: {fate.name(f, x) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.find(deps.of(Up.deps.join(f, r)), m) == M.find(deps.of(r), m) : M.Dep}

# LAW: a dependency of another name, in front of the rest, is passed over
law skip_find:
  for d: M.Dep
  for +ds: List<&2, M.Dep>
  for +x: String
  for +m: String
  for nf: {M.dep.name(d) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.find(d <> ds, m) == M.find(ds, m) : M.Dep}

def skip_find(d, ds, x, m, nf, ne):
  match d:
    case M.Dep{+dn, +dh, +de, +dsrc}:
      nfs = Equal.sym(String, dn, x, nf)
      %nfs : {M.find.pick(String.eq(_, m), M.Dep{dn, dh, de, dsrc}, M.find(ds, m))
        == M.find(ds, m) : M.Dep}
      nes = Equal.sym(Bool, String.eq(x, m), False{}, ne)
      %nes : {M.find.pick(_, M.Dep{dn, dh, de, dsrc}, M.find(ds, m))
        == M.find(ds, m) : M.Dep}
      {==}

def join_skip(f, r, x, m, nf, ne):
  match f:
    case Up.Became{d, old, new, prev, mv, says, trees}:
      match r:
        case Up.Deps{+ds, ss, es, any, sy, tr, asks, bad}:
          skip_find(d, ds, x, m, nf, ne)
    case Up.Waits{more}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}
    case Up.Halts{why}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}

# LAW: an entry that is held, joined in front of the rest, is the one a lookup
# of its name finds
law held_find:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +hs: M.Source
  for r: Up.Deps
  for +m: String
  for e: {String.eq(hn, m) == True{} : Bool}
  for h: {aim == U.Hold{} : U.Aim}
  {M.find(deps.of(Up.deps.join(Up.dep.one(aim, rs, only, hub, M.Dep{hn, hh, he, hs}), r)), m)
    == M.Dep{hn, hh, he, hs} : M.Dep}

def held_find(aim, rs, only, hub, hn, hh, he, hs, r, m, e, h):
  match r:
    case Up.Deps{+ds, +ss, +es, +any, +sy, +tr, +asks, +bad}:
      hsym = Equal.sym(U.Aim, aim, U.Hold{}, h)
      %hsym : {M.find(deps.of(Up.deps.join(Up.dep.one(_, rs, only, hub, M.Dep{hn, hh, he, hs}),
        Up.Deps{ds, ss, es, any, sy, tr, asks, bad})), m) == M.Dep{hn, hh, he, hs} : M.Dep}
      es2 = Equal.sym(Bool, String.eq(hn, m), True{}, e)
      %es2 : {M.find.pick(_, M.Dep{hn, hh, he, hs}, M.find(ds, m)) == M.Dep{hn, hh, he, hs} : M.Dep}
      {==}

# LAW: one dependency of the walk. Its name either is the one looked up, and
# then it is held and found as it was, or it is not, and the lookup goes on to
# the rest, which the walk leaves as it found it.
law find_walk.hit:
  for hit: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +hs: M.Source
  for +t: List<&2, M.Dep>
  for +m: String
  for +e: {String.eq(hn, m) == hit : Bool}
  for pre: {U.aim(U.chosen(only, m),
    M.source.dep(M.find.pick(hit, M.Dep{hn, hh, he, hs}, M.find(t, m)))) == U.Hold{} : U.Aim}
  for ih: {U.aim(U.chosen(only, m), M.source.dep(M.find(t, m))) == U.Hold{} : U.Aim}
    -> {M.find(deps.of(Up.deps.walk(rs, only, hub, t)), m) == M.find(t, m) : M.Dep}
  {M.find(deps.of(Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), hs), rs, only, hub,
    M.Dep{hn, hh, he, hs}), Up.deps.walk(rs, only, hub, t))), m)
    == M.find.pick(hit, M.Dep{hn, hh, he, hs}, M.find(t, m)) : M.Dep}

def find_walk.hit(hit, rs, only, hub, hn, hh, he, hs, t, m, e, pre, ih):
  match hit:
    case True{}:
      held_find(U.aim(U.chosen(only, hn), hs), rs, only, hub, hn, hh, he, hs,
        Up.deps.walk(rs, only, hub, t), m, e,
        Equal.trans(U.Aim, U.aim(U.chosen(only, hn), hs), U.aim(U.chosen(only, m), hs), U.Hold{},
          Equal.cong(String, U.Aim, x => U.aim(U.chosen(only, x), hs), hn, m,
            Str.string_eq_true(hn, m, e)),
          pre))
    case False{}:
      Equal.trans(M.Dep,
        M.find(deps.of(Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), hs), rs, only, hub,
          M.Dep{hn, hh, he, hs}), Up.deps.walk(rs, only, hub, t))), m),
        M.find(deps.of(Up.deps.walk(rs, only, hub, t)), m),
        M.find(t, m),
        join_skip(Up.dep.one(U.aim(U.chosen(only, hn), hs), rs, only, hub, M.Dep{hn, hh, he, hs}),
          Up.deps.walk(rs, only, hub, t), hn, m,
          one_name(U.aim(U.chosen(only, hn), hs), rs, only, hub, M.Dep{hn, hh, he, hs}), e),
        ih(pre))

# LAW: the walk leaves the dependency a name finds as it was, when that
# dependency is held
law find_walk:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for ds: List<&2, M.Dep>
  for +m: String
  for pre: {U.aim(U.chosen(only, m), M.source.dep(M.find(ds, m))) == U.Hold{} : U.Aim}
  {M.find(deps.of(Up.deps.walk(rs, only, hub, ds)), m) == M.find(ds, m) : M.Dep}

def find_walk(rs, only, hub, ds, m, pre):
  match ds:
    case []:
      {==}
    case h <> +t:
      match h:
        case M.Dep{+hn, +hh, +he, +hs}:
          find_walk.hit(String.eq(hn, m), rs, only, hub, hn, hh, he, hs, t, m, {==}, pre,
            p => find_walk(rs, only, hub, t, m, p))

# The pipeline. `Up.next` walks the dependencies and the tools, and then
# either stops, with ez.toml's model as it was, or renders the model with the
# walked lists in place of the old ones. So anything read off the model that
# the walked lists leave as it was, the upgrade leaves as it was. Each lemma
# is one def of the pipeline, with the value it branches on as a parameter.

# the tools a walk leaves
def tools.of(tt: Up.Tools) -> List<&2, M.Tool>:
  Up.Tools{ts, _m, _sy, _asks, _bad} = tt
  ts

# LAW: the model an upgrade renders, or the old one
law model_kept:
  for A: Type
  for f: M.Read -> A
  for moved: Bool
  for +next: M.Manifest
  for +old: M.Manifest
  for pre: {f(M.Good{next}) == f(M.Good{old}) : A}
  {f(Up.model.next(moved, next, old)) == f(M.Good{old}) : A}

def model_kept(_A, _f, moved, _next, _old, pre):
  match moved:
    case True{}:
      pre
    case False{}:
      {==}

law done_kept:
  for A: Type
  for f: M.Read -> A
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ignore: String
  for fs: List<&2, Up.Found>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.done(M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt, ignore, fs)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def done_kept(A, f, pn, pe, pb, hb, ods, ots, dd, tt, _ignore, _fs, pre):
  match dd:
    case Up.Deps{+ds, ss, es, dm, dsy, dtr, das, dbad}:
      match tt:
        case Up.Tools{+ts, tm, tsy, tas, tbad}:
          model_kept(A, f, Bool.or(dm, tm), M.Manifest{pn, pe, pb, hb, ds, ts},
            M.Manifest{pn, pe, pb, hb, ods, ots}, pre)

law srcs_kept:
  for A: Type
  for f: M.Read -> A
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ignore: String
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt, ignore)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def srcs_kept(A, f, srcs, pn, pe, pb, hb, ods, ots, dd, tt, ignore, pre):
  match srcs:
    case Up.Srcs{fs}:
      done_kept(A, f, pn, pe, pb, hb, ods, ots, dd, tt, ignore, fs, pre)
    case Up.SrcsWait{_ask}:
      {==}
    case Up.SrcsNo{_why}:
      {==}

law ignore_kept:
  for A: Type
  for f: M.Read -> A
  for said: Up.Said
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.got.ignore(said, srcs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def ignore_kept(A, f, said, srcs, pn, pe, pb, hb, ods, ots, dd, tt, pre):
  match said:
    case Up.Said{ignore}:
      srcs_kept(A, f, srcs, pn, pe, pb, hb, ods, ots, dd, tt, ignore, pre)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law asks_kept:
  for A: Type
  for f: M.Read -> A
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for tt: Up.Tools
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.pins.asks(asks, rs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def asks_kept(A, f, asks, rs, pn, pe, pb, hb, ods, ots, dd, tt, pre):
  match asks:
    case []:
      ignore_kept(A, f, Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd)), rs),
        pn, pe, pb, hb, ods, ots, dd, tt, pre)
    case _h <> _t:
      {==}

law bad_kept:
  for A: Type
  for f: M.Read -> A
  for clean: Bool
  for bad: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for tt: Up.Tools
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.pins.bad(clean, bad, asks, rs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def bad_kept(A, f, clean, _bad, asks, rs, pn, pe, pb, hb, ods, ots, dd, tt, pre):
  match clean:
    case True{}:
      asks_kept(A, f, asks, rs, pn, pe, pb, hb, ods, ots, dd, tt, pre)
    case False{}:
      {==}

law pins_kept:
  for A: Type
  for f: M.Read -> A
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.pins(dd, tt, rs, M.Manifest{pn, pe, pb, hb, ods, ots})))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def pins_kept(A, f, dd, tt, rs, pn, pe, pb, hb, ods, ots, pre):
  match dd:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad}:
      match tt:
        case Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
          bad_kept(A, f, Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            List.append(&2, Up.Ask, das, tas), rs, pn, pe, pb, hb, ods, ots,
            Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}, pre)

law next_kept.known:
  for A: Type
  for f: M.Read -> A
  for ok: Bool
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb,
    deps.of(Up.deps.walk(rs, only, M.hub.or(hb), ods)), tools.of(Up.tools.walk(rs, only, ots))}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.known(ok, only, rs, M.Manifest{pn, pe, pb, hb, ods, ots})))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def next_kept.known(A, f, ok, only, rs, pn, pe, pb, hb, ods, ots, pre):
  match ok:
    case False{}:
      {==}
    case True{}:
      pins_kept(A, f, Up.deps.walk(rs, only, M.hub.or(hb), ods), Up.tools.walk(rs, only, ots), rs,
        pn, pe, pb, hb, ods, ots, pre)

# LAW: whatever `--package` named and whatever the remote said, the model an
# upgrade leaves reads, through `f`, as ez.toml's does, once the walked lists
# read so
law next_kept:
  for A: Type
  for f: M.Read -> A
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb,
    deps.of(Up.deps.walk(rs, only, M.hub.or(hb), ods)), tools.of(Up.tools.walk(rs, only, ots))}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}
  {f(Up.next.model(Up.next(only, M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}, rs)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, ods, ots}}) : A}

def next_kept(A, f, only, rs, pn, pe, pb, hb, ods, ots, pre):
  next_kept.known(A, f, Bool.or(U.known(only, ods), M.tool.known(only, ots)), only, rs,
    pn, pe, pb, hb, ods, ots, pre)

# EZ-RES-4. A hub dependency is held whether `--package` chose it or not, so
# the walk leaves the dependency its name finds as it was, and so does the
# model. A plain lock's model is ez.toml's.

law hub_read:
  for +only: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +n: String
  for pre: {M.source.is_git(M.source.dep(M.dep(r, n))) == False{} : Bool}
  {M.dep(Up.next.model(Up.next(only, r, rs)), n) == M.dep(r, n) : M.Dep}

def hub_read(only, r, rs, n, pre):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{+pn, +pe, +pb, +hb, +ods, +ots}:
          next_kept(M.Dep, x => M.dep(x, n), only, rs, pn, pe, pb, hb, ods, ots,
            find_walk(rs, only, M.hub.or(hb), ods, n,
              hub_holds(U.chosen(only, n), M.source.dep(M.find(ods, n)), pre)))

def Laws.upgrade_holds_hub(w, n, pre):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              {==}
            case True{}:
              hub_read(only, W.parsed(ledger), ups, n, pre)

# EZ-RES-6, the dependencies. One of another name is not chosen, so it is
# held, and the walk leaves it as it was.

law frame_read:
  for +n: String
  for +m: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +ne: {String.is_empty(n) == False{} : Bool}
  for +d: {String.eq(n, m) == False{} : Bool}
  {M.dep(Up.next.model(Up.next(n, r, rs)), m) == M.dep(r, m) : M.Dep}

def frame_read(n, m, r, rs, ne, d):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{mm}:
      match mm:
        case M.Manifest{+pn, +pe, +pb, +hb, +ods, +ots}:
          next_kept(M.Dep, x => M.dep(x, m), n, rs, pn, pe, pb, hb, ods, ots,
            find_walk(rs, n, M.hub.or(hb), ods, m,
              unchosen_holds(n, m, M.source.dep(M.find(ods, m)), ne, d)))

def Laws.upgrade_one_frames_deps(w, n, m, e, ne, d):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              {==}
            case True{}:
              es = Equal.sym(String, only, n, e)
              %es : {M.dep(Up.next.model(Up.next(_, W.parsed(ledger), ups)), m)
                == M.dep(W.parsed(ledger), m) : M.Dep}
              frame_read(n, m, W.parsed(ledger), ups, ne, d)

# EZ-RES-6, the tools, in the shape of the dependencies above: one tool's
# pin keeps its name, and one of another name is not chosen, so it is left.

# the name a tool's pin leaves in the ledger, or `x` when it leaves none
def pinned.name(p: Up.Pinned, x: String) -> String:
  match p:
    case Up.Pinned{t, _moved, _says}:
      M.tool.name(t)
    case Up.PinWait{_asks}:
      x
    case Up.PinHalt{_why}:
      x

# LAW: a pin with a commit written in keeps its name
law set_name:
  for tool: M.Tool
  for rev: String
  for tag: String
  for nar: String
  {M.tool.name(Up.set(tool, rev, tag, nar)) == M.tool.name(tool) : String}

def set_name(tool, _rev, _tag, _nar):
  match tool:
    case M.Tool{n, e, b, s}:
      match s:
        case M.Hub{}:
          {==}
        case M.Git{url, r, old, root, nr, vend}:
          {==}

law weighed_name:
  for wd: Up.Wd
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {pinned.name(Up.tool.weighed(wd, tool, rev, tag, says), M.tool.name(tool))
    == M.tool.name(tool) : String}

def weighed_name(wd, tool, rev, tag, _says):
  match wd:
    case Up.Wd{nar}:
      set_name(tool, rev, tag, nar)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.resolved(tip, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def resolved_name(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, _branch}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, tag, [])
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law named_name:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +url: String
  {pinned.name(Up.tool.named(named, rs, tool, url), M.tool.name(tool)) == M.tool.name(tool) : String}

def named_name(named, rs, tool, url):
  match named:
    case Up.Named{ref}:
      resolved_name(Up.follow(rs, url, ref), rs, tool)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

law fill_name:
  for no_rev: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.fill(no_rev, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def fill_name(no_rev, rs, tool):
  match no_rev:
    case True{}:
      named_name(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(tool))), rs,
        M.source.url(M.tool.source(tool)), M.source.tag(M.tool.source(tool))), rs, tool,
        M.source.url(M.tool.source(tool)))
    case False{}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), tool, M.source.rev(M.tool.source(tool)), "", [])

law tverdict_name:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +branch: String
  {pinned.name(Up.tool.verdict(verdict, rs, tool, tip, branch), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tverdict_name(verdict, rs, tool, _tip, branch):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, tag}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, tag,
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_name:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  {pinned.name(Up.tool.kept(wd, rs, tool, tip, tag), M.tool.name(tool)) == M.tool.name(tool) : String}

def tkept_name(wd, rs, tool, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      tverdict_name(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law tonward_name:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +branch: String
  {pinned.name(Up.tool.onward(asc, rs, tool, tip, tag, branch), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tonward_name(asc, rs, tool, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      tverdict_name(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law tsame_name:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +branch: String
  {pinned.name(Up.tool.same(same, rs, tool, tip, tag, branch), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tsame_name(same, rs, tool, tip, tag, branch):
  match same:
    case True{}:
      tkept_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), rs, tool, tip, tag)
    case False{}:
      tonward_name(Up.onward(rs, Up.Above{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool)), tip}), rs, tool, tip, tag, branch)

law ttip_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.tip(tip, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def ttip_name(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, branch}:
      tsame_name(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law taim_name:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.aim(aim, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def taim_name(aim, rs, tool):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      ttip_name(Up.follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      ttip_name(Up.forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

law short_name:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.short(short, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def short_name(short, rs, tool):
  match short:
    case True{}:
      fill_name(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      taim_name(U.aim(True{}, M.tool.source(tool)), rs, tool)

law git_name:
  for git: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.git(git, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def git_name(git, rs, tool):
  match git:
    case False{}:
      {==}
    case True{}:
      short_name(Bool.or(String.is_empty(M.source.rev(M.tool.source(tool))),
        String.is_empty(M.source.nar(M.tool.source(tool)))), rs, tool)

# LAW: whatever the upgrade makes of one tool, what it leaves in the ledger has
# the tool's name
law sel_name:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pinned.name(Up.tool.sel(sel, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def sel_name(sel, rs, tool):
  match sel:
    case False{}:
      {==}
    case True{}:
      git_name(M.source.is_git(M.tool.source(tool)), rs, tool)

# LAW: a tool of another name, in front of the rest, is passed over
law tskip_find:
  for t: M.Tool
  for +ts: List<&2, M.Tool>
  for +x: String
  for +m: String
  for nf: {M.tool.name(t) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.tool.find(t <> ts, m) == M.tool.find(ts, m) : M.Tool}

def tskip_find(t, ts, x, m, nf, ne):
  match t:
    case M.Tool{+tn, +te, +tb, +tsrc}:
      nfs = Equal.sym(String, tn, x, nf)
      %nfs : {M.tool.find.pick(String.eq(_, m), M.Tool{tn, te, tb, tsrc}, M.tool.find(ts, m))
        == M.tool.find(ts, m) : M.Tool}
      nes = Equal.sym(Bool, String.eq(x, m), False{}, ne)
      %nes : {M.tool.find.pick(_, M.Tool{tn, te, tb, tsrc}, M.tool.find(ts, m))
        == M.tool.find(ts, m) : M.Tool}
      {==}

# LAW: a pin of another name, joined in front of the rest, is passed over by
# a lookup
law tjoin_skip:
  for p: Up.Pinned
  for r: Up.Tools
  for +x: String
  for +m: String
  for nf: {pinned.name(p, x) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.tool.find(tools.of(Up.tools.join(p, r)), m) == M.tool.find(tools.of(r), m) : M.Tool}

def tjoin_skip(p, r, x, m, nf, ne):
  match p:
    case Up.Pinned{t, mv, says}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          tskip_find(t, ts, x, m, nf, ne)
    case Up.PinWait{more}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}
    case Up.PinHalt{why}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}

# LAW: a tool that is not chosen, joined in front of the rest, is the one a
# lookup of its name finds
law left_find:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tn: String
  for +te: String
  for +tb: String
  for +tsrc: M.Source
  for r: Up.Tools
  for +m: String
  for e: {String.eq(tn, m) == True{} : Bool}
  for h: {sel == False{} : Bool}
  {M.tool.find(tools.of(Up.tools.join(Up.tool.sel(sel, rs, M.Tool{tn, te, tb, tsrc}), r)), m)
    == M.Tool{tn, te, tb, tsrc} : M.Tool}

def left_find(sel, rs, tn, te, tb, tsrc, r, m, e, h):
  match r:
    case Up.Tools{+ts, +any, +sy, +asks, +bad}:
      hsym = Equal.sym(Bool, sel, False{}, h)
      %hsym : {M.tool.find(tools.of(Up.tools.join(Up.tool.sel(_, rs, M.Tool{tn, te, tb, tsrc}),
        Up.Tools{ts, any, sy, asks, bad})), m) == M.Tool{tn, te, tb, tsrc} : M.Tool}
      es2 = Equal.sym(Bool, String.eq(tn, m), True{}, e)
      %es2 : {M.tool.find.pick(_, M.Tool{tn, te, tb, tsrc}, M.tool.find(ts, m))
        == M.Tool{tn, te, tb, tsrc} : M.Tool}
      {==}

law tfind_walk.hit:
  for hit: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +tn: String
  for +te: String
  for +tb: String
  for +tsrc: M.Source
  for +t: List<&2, M.Tool>
  for +m: String
  for +e: {String.eq(tn, m) == hit : Bool}
  for pre: {U.chosen(only, m) == False{} : Bool}
  for ih: {M.tool.find(tools.of(Up.tools.walk(rs, only, t)), m) == M.tool.find(t, m) : M.Tool}
  {M.tool.find(tools.of(Up.tools.join(Up.tool.sel(U.chosen(only, tn), rs, M.Tool{tn, te, tb, tsrc}),
    Up.tools.walk(rs, only, t))), m)
    == M.tool.find.pick(hit, M.Tool{tn, te, tb, tsrc}, M.tool.find(t, m)) : M.Tool}

def tfind_walk.hit(hit, rs, only, tn, te, tb, tsrc, t, m, e, pre, ih):
  match hit:
    case True{}:
      left_find(U.chosen(only, tn), rs, tn, te, tb, tsrc, Up.tools.walk(rs, only, t), m, e,
        Equal.trans(Bool, U.chosen(only, tn), U.chosen(only, m), False{},
          Equal.cong(String, Bool, x => U.chosen(only, x), tn, m, Str.string_eq_true(tn, m, e)),
          pre))
    case False{}:
      Equal.trans(M.Tool,
        M.tool.find(tools.of(Up.tools.join(Up.tool.sel(U.chosen(only, tn), rs,
          M.Tool{tn, te, tb, tsrc}), Up.tools.walk(rs, only, t))), m),
        M.tool.find(tools.of(Up.tools.walk(rs, only, t)), m),
        M.tool.find(t, m),
        tjoin_skip(Up.tool.sel(U.chosen(only, tn), rs, M.Tool{tn, te, tb, tsrc}),
          Up.tools.walk(rs, only, t), tn, m,
          sel_name(U.chosen(only, tn), rs, M.Tool{tn, te, tb, tsrc}), e),
        ih)

# LAW: the walk leaves every tool of a name `--package` does not choose as it
# was
law tfind_walk:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for ts: List<&2, M.Tool>
  for +m: String
  for +pre: {U.chosen(only, m) == False{} : Bool}
  {M.tool.find(tools.of(Up.tools.walk(rs, only, ts)), m) == M.tool.find(ts, m) : M.Tool}

def tfind_walk(rs, only, ts, m, pre):
  match ts:
    case []:
      {==}
    case h <> +t:
      match h:
        case M.Tool{+tn, +te, +tb, +tsrc}:
          tfind_walk.hit(String.eq(tn, m), rs, only, tn, te, tb, tsrc, t, m, {==}, pre,
            tfind_walk(rs, only, t, m, pre))

law tframe_read:
  for +n: String
  for +m: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for ne: {String.is_empty(n) == False{} : Bool}
  for d: {String.eq(n, m) == False{} : Bool}
  {Laws.tool.at(Up.next.model(Up.next(n, r, rs)), m) == Laws.tool.at(r, m) : M.Tool}

def tframe_read(n, m, r, rs, ne, d):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{mm}:
      match mm:
        case M.Manifest{+pn, +pe, +pb, +hb, +ods, +ots}:
          next_kept(M.Tool, x => Laws.tool.at(x, m), n, rs, pn, pe, pb, hb, ods, ots,
            tfind_walk(rs, n, ots, m, unchosen(n, m, ne, d)))

def Laws.upgrade_one_frames_tools(w, n, m, e, ne, d):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              {==}
            case True{}:
              es = Equal.sym(String, only, n, e)
              %es : {Laws.tool.at(Up.next.model(Up.next(_, W.parsed(ledger), ups)), m)
                == Laws.tool.at(W.parsed(ledger), m) : M.Tool}
              tframe_read(n, m, W.parsed(ledger), ups, ne, d)

# EZ-RES-6, the questions. What the upgrade asks is read off the two walks
# only through their keys: the questions each left open, its refusal, and the
# hashes import lines stop naming. An entry `--package` does not choose is
# held, and a held entry adds nothing to any of the three, so the walk over
# the ledger and the walk over the entries named `n` alone have the same
# keys, and the pipeline asks the same questions of both.

# the part of a dependency walk the questions depend on
def dkey(dd: Up.Deps) -> Up.Deps:
  Up.Deps{_ds, _ss, es, _m, _sy, _tr, asks, bad} = dd
  Up.Deps{[], [], es, False{}, [], [], asks, bad}

# and of a tool walk
def tkey(tt: Up.Tools) -> Up.Tools:
  Up.Tools{_ts, _m, _sy, asks, bad} = tt
  Up.Tools{[], False{}, [], asks, bad}

# LAW: one dependency joined in front of a walk adds to its key what it adds
# to the key alone
law djoin_key:
  for f: Up.Fate
  for r: Up.Deps
  {dkey(Up.deps.join(f, r)) == dkey(Up.deps.join(f, dkey(r))) : Up.Deps}

def djoin_key(f, r):
  match f:
    case Up.Became{d, old, new, prev, mv, says, trees}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}
    case Up.Waits{more}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}
    case Up.Halts{why}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}

# LAW: so two walks with one key, each with the same dependency in front,
# still have one key
law djoin_cong:
  for +f: Up.Fate
  for +r1: Up.Deps
  for +r2: Up.Deps
  for ih: {dkey(r1) == dkey(r2) : Up.Deps}
  {dkey(Up.deps.join(f, r1)) == dkey(Up.deps.join(f, r2)) : Up.Deps}

def djoin_cong(f, r1, r2, ih):
  Equal.trans(Up.Deps, dkey(Up.deps.join(f, r1)), dkey(Up.deps.join(f, dkey(r1))),
    dkey(Up.deps.join(f, r2)),
    djoin_key(f, r1),
    Equal.trans(Up.Deps, dkey(Up.deps.join(f, dkey(r1))), dkey(Up.deps.join(f, dkey(r2))),
      dkey(Up.deps.join(f, r2)),
      Equal.cong(Up.Deps, Up.Deps, k => dkey(Up.deps.join(f, k)), dkey(r1), dkey(r2), ih),
      Equal.sym(Up.Deps, dkey(Up.deps.join(f, r2)), dkey(Up.deps.join(f, dkey(r2))),
        djoin_key(f, r2))))

# LAW: a held dependency adds nothing to the key
law ddrop:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for r: Up.Deps
  {dkey(Up.deps.join(Up.dep.one(U.Hold{}, rs, only, hub, h), r)) == dkey(r) : Up.Deps}

def ddrop(_rs, _only, _hub, _h, r):
  match r:
    case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
      {==}

law dalone_walk.hit:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hub: String
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for e: {b == U.chosen(n, M.dep.name(h)) : Bool}
  for ih: {dkey(Up.deps.walk(rs, n, hub, t)) == dkey(Up.deps.walk(rs, n, hub, Laws.deps.named(t, n)))
    : Up.Deps}
  {dkey(Up.deps.walk(rs, n, hub, h <> t))
    == dkey(Up.deps.walk(rs, n, hub, Laws.deps.put(b, h, Laws.deps.named(t, n)))) : Up.Deps}

def dalone_walk.hit(b, rs, n, hub, h, t, e, ih):
  match b:
    case True{}:
      djoin_cong(Up.dep.one(U.aim(U.chosen(n, M.dep.name(h)), M.source.dep(h)), rs, n, hub, h),
        Up.deps.walk(rs, n, hub, t), Up.deps.walk(rs, n, hub, Laws.deps.named(t, n)), ih)
    case False{}:
      %e : {dkey(Up.deps.join(Up.dep.one(U.aim(_, M.source.dep(h)), rs, n, hub, h),
        Up.deps.walk(rs, n, hub, t)))
        == dkey(Up.deps.walk(rs, n, hub, Laws.deps.named(t, n))) : Up.Deps}
      Equal.trans(Up.Deps,
        dkey(Up.deps.join(Up.dep.one(U.Hold{}, rs, n, hub, h), Up.deps.walk(rs, n, hub, t))),
        dkey(Up.deps.walk(rs, n, hub, t)),
        dkey(Up.deps.walk(rs, n, hub, Laws.deps.named(t, n))),
        ddrop(rs, n, hub, h, Up.deps.walk(rs, n, hub, t)),
        ih)

# LAW: the walk over a ledger's dependencies and the walk over those named
# `n` alone have one key
law dalone_walk:
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hub: String
  for ds: List<&2, M.Dep>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {dkey(Up.deps.walk(rs, n, hub, ds)) == dkey(Up.deps.walk(rs, n, hub, Laws.deps.named(ds, n)))
    : Up.Deps}

def dalone_walk(rs, n, hub, ds, ne):
  match ds:
    case []:
      {==}
    case +h <> +t:
      dalone_walk.hit(String.eq(M.dep.name(h), n), rs, n, hub, h, t,
        Equal.sym(Bool, U.chosen(n, M.dep.name(h)), String.eq(M.dep.name(h), n),
          chosen_named(n, M.dep.name(h), ne)),
        dalone_walk(rs, n, hub, t, ne))

# LAW: and the tools, the same way
law tjoin_key:
  for p: Up.Pinned
  for r: Up.Tools
  {tkey(Up.tools.join(p, r)) == tkey(Up.tools.join(p, tkey(r))) : Up.Tools}

def tjoin_key(p, r):
  match p:
    case Up.Pinned{t, mv, says}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}
    case Up.PinWait{more}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}
    case Up.PinHalt{why}:
      match r:
        case Up.Tools{ts, any, sy, asks, bad}:
          {==}

law tjoin_cong:
  for +p: Up.Pinned
  for +r1: Up.Tools
  for +r2: Up.Tools
  for ih: {tkey(r1) == tkey(r2) : Up.Tools}
  {tkey(Up.tools.join(p, r1)) == tkey(Up.tools.join(p, r2)) : Up.Tools}

def tjoin_cong(p, r1, r2, ih):
  Equal.trans(Up.Tools, tkey(Up.tools.join(p, r1)), tkey(Up.tools.join(p, tkey(r1))),
    tkey(Up.tools.join(p, r2)),
    tjoin_key(p, r1),
    Equal.trans(Up.Tools, tkey(Up.tools.join(p, tkey(r1))), tkey(Up.tools.join(p, tkey(r2))),
      tkey(Up.tools.join(p, r2)),
      Equal.cong(Up.Tools, Up.Tools, k => tkey(Up.tools.join(p, k)), tkey(r1), tkey(r2), ih),
      Equal.sym(Up.Tools, tkey(Up.tools.join(p, r2)), tkey(Up.tools.join(p, tkey(r2))),
        tjoin_key(p, r2))))

law tdrop:
  for +rs: List<&2, Up.Reply>
  for +h: M.Tool
  for r: Up.Tools
  {tkey(Up.tools.join(Up.tool.sel(False{}, rs, h), r)) == tkey(r) : Up.Tools}

def tdrop(_rs, _h, r):
  match r:
    case Up.Tools{ts, any, sy, asks, bad}:
      {==}

law talone_walk.hit:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for e: {b == U.chosen(n, M.tool.name(h)) : Bool}
  for ih: {tkey(Up.tools.walk(rs, n, t)) == tkey(Up.tools.walk(rs, n, Laws.tools.named(t, n)))
    : Up.Tools}
  {tkey(Up.tools.walk(rs, n, h <> t))
    == tkey(Up.tools.walk(rs, n, Laws.tools.put(b, h, Laws.tools.named(t, n)))) : Up.Tools}

def talone_walk.hit(b, rs, n, h, t, e, ih):
  match b:
    case True{}:
      tjoin_cong(Up.tool.sel(U.chosen(n, M.tool.name(h)), rs, h),
        Up.tools.walk(rs, n, t), Up.tools.walk(rs, n, Laws.tools.named(t, n)), ih)
    case False{}:
      %e : {tkey(Up.tools.join(Up.tool.sel(_, rs, h), Up.tools.walk(rs, n, t)))
        == tkey(Up.tools.walk(rs, n, Laws.tools.named(t, n))) : Up.Tools}
      Equal.trans(Up.Tools,
        tkey(Up.tools.join(Up.tool.sel(False{}, rs, h), Up.tools.walk(rs, n, t))),
        tkey(Up.tools.walk(rs, n, t)),
        tkey(Up.tools.walk(rs, n, Laws.tools.named(t, n))),
        tdrop(rs, h, Up.tools.walk(rs, n, t)),
        ih)

law talone_walk:
  for +rs: List<&2, Up.Reply>
  for +n: String
  for ts: List<&2, M.Tool>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {tkey(Up.tools.walk(rs, n, ts)) == tkey(Up.tools.walk(rs, n, Laws.tools.named(ts, n)))
    : Up.Tools}

def talone_walk(rs, n, ts, ne):
  match ts:
    case []:
      {==}
    case +h <> +t:
      talone_walk.hit(String.eq(M.tool.name(h), n), rs, n, h, t,
        Equal.sym(Bool, U.chosen(n, M.tool.name(h)), String.eq(M.tool.name(h), n),
          chosen_named(n, M.tool.name(h), ne)),
        talone_walk(rs, n, t, ne))

# `--package n` is checked against the ledger before anything is asked. The
# entries named `n` are all of them that can answer that check.

law kin.hit:
  for b: Bool
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +n: String
  for e: {b == String.eq(M.dep.name(h), n) : Bool}
  for ih: {U.known.in(t, n) == U.known.in(Laws.deps.named(t, n), n) : Bool}
  {U.known.step(b, _u => U.known.in(t, n))
    == U.known.in(Laws.deps.put(b, h, Laws.deps.named(t, n)), n) : Bool}

def kin.hit(b, _h, t, n, e, ih):
  match b:
    case True{}:
      %e : {True{} == U.known.step(_, _u => U.known.in(Laws.deps.named(t, n), n)) : Bool}
      {==}
    case False{}:
      ih

law kin:
  for ds: List<&2, M.Dep>
  for +n: String
  {U.known.in(ds, n) == U.known.in(Laws.deps.named(ds, n), n) : Bool}

def kin(ds, n):
  match ds:
    case []:
      {==}
    case +h <> +t:
      kin.hit(String.eq(M.dep.name(h), n), h, t, n, {==}, kin(t, n))

# LAW: the ledger names the dependency `--package n` asks for exactly when
# its entries named `n` do
law dknown:
  for +n: String
  for +ds: List<&2, M.Dep>
  for ne: {String.is_empty(n) == False{} : Bool}
  {U.known(n, ds) == U.known(n, Laws.deps.named(ds, n)) : Bool}

def dknown(n, ds, ne):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {U.known.go(_, ds, n) == U.known.go(_, Laws.deps.named(ds, n), n) : Bool}
  kin(ds, n)

law tkin.hit:
  for b: Bool
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for +n: String
  for e: {b == String.eq(M.tool.name(h), n) : Bool}
  for ih: {M.tool.has(t, n) == M.tool.has(Laws.tools.named(t, n), n) : Bool}
  {M.tool.step(b, _u => M.tool.has(t, n))
    == M.tool.has(Laws.tools.put(b, h, Laws.tools.named(t, n)), n) : Bool}

def tkin.hit(b, _h, t, n, e, ih):
  match b:
    case True{}:
      %e : {True{} == M.tool.step(_, _u => M.tool.has(Laws.tools.named(t, n), n)) : Bool}
      {==}
    case False{}:
      ih

law tkin:
  for ts: List<&2, M.Tool>
  for +n: String
  {M.tool.has(ts, n) == M.tool.has(Laws.tools.named(ts, n), n) : Bool}

def tkin(ts, n):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tkin.hit(String.eq(M.tool.name(h), n), h, t, n, {==}, tkin(t, n))

law tknown:
  for +n: String
  for +ts: List<&2, M.Tool>
  for ne: {String.is_empty(n) == False{} : Bool}
  {M.tool.known(n, ts) == M.tool.known(n, Laws.tools.named(ts, n)) : Bool}

def tknown(n, ts, ne):
  nes = Equal.sym(Bool, String.is_empty(n), False{}, ne)
  %nes : {M.tool.known.go(_, ts, n) == M.tool.known.go(_, Laws.tools.named(ts, n), n) : Bool}
  tkin(ts, n)

# The pipeline's questions: after the walks, the upgrade asks for
# `.gitignore` and the sources, or stops, and neither depends on anything but
# the walks' keys.

law asks_done:
  for old1: M.Manifest
  for old2: M.Manifest
  for dd1: Up.Deps
  for dd2: Up.Deps
  for tt1: Up.Tools
  for tt2: Up.Tools
  for +ignore: String
  for +fs: List<&2, Up.Found>
  {Up.next.asks(Up.done(old1, dd1, tt1, ignore, fs)) == Up.next.asks(Up.done(old2, dd2, tt2, ignore, fs))
    : List<&2, Up.Ask>}

def asks_done(old1, old2, dd1, dd2, tt1, tt2, _ignore, _fs):
  match old1:
    case M.Manifest{n1, e1, b1, h1, ds1, ts1}:
      match old2:
        case M.Manifest{n2, e2, b2, h2, ds2, ts2}:
          match dd1:
            case Up.Deps{a1, s1, x1, m1, y1, r1, k1, d1}:
              match dd2:
                case Up.Deps{a2, s2, x2, m2, y2, r2, k2, d2}:
                  match tt1:
                    case Up.Tools{u1, v1, w1, p1, q1}:
                      match tt2:
                        case Up.Tools{u2, v2, w2, p2, q2}:
                          {==}

law asks_srcs:
  for srcs: Up.Srcs
  for old1: M.Manifest
  for old2: M.Manifest
  for dd1: Up.Deps
  for dd2: Up.Deps
  for tt1: Up.Tools
  for tt2: Up.Tools
  for +ignore: String
  {Up.next.asks(Up.got.srcs(srcs, old1, dd1, tt1, ignore))
    == Up.next.asks(Up.got.srcs(srcs, old2, dd2, tt2, ignore)) : List<&2, Up.Ask>}

def asks_srcs(srcs, old1, old2, dd1, dd2, tt1, tt2, ignore):
  match srcs:
    case Up.Srcs{fs}:
      asks_done(old1, old2, dd1, dd2, tt1, tt2, ignore, fs)
    case Up.SrcsWait{_ask}:
      {==}
    case Up.SrcsNo{_why}:
      {==}

law asks_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for old1: M.Manifest
  for old2: M.Manifest
  for dd1: Up.Deps
  for dd2: Up.Deps
  for tt1: Up.Tools
  for tt2: Up.Tools
  {Up.next.asks(Up.got.ignore(said, srcs, old1, dd1, tt1))
    == Up.next.asks(Up.got.ignore(said, srcs, old2, dd2, tt2)) : List<&2, Up.Ask>}

def asks_ignore(said, srcs, old1, old2, dd1, dd2, tt1, tt2):
  match said:
    case Up.Said{+ignore}:
      asks_srcs(srcs, old1, old2, dd1, dd2, tt1, tt2, ignore)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law asks_settled:
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for +dd1: Up.Deps
  for +dd2: Up.Deps
  for +tt1: Up.Tools
  for +tt2: Up.Tools
  for e: {Up.deps.edits(dd1) == Up.deps.edits(dd2) : List<&2, U.Swap>}
  {Up.next.asks(Up.settled(rs, old1, dd1, tt1)) == Up.next.asks(Up.settled(rs, old2, dd2, tt2))
    : List<&2, Up.Ask>}

def asks_settled(rs, old1, old2, dd1, dd2, tt1, tt2, e):
  %e : {Up.next.asks(Up.settled(rs, old1, dd1, tt1))
    == Up.next.asks(Up.got.ignore(Up.text.said(rs, Up.Ignore{}),
      Up.ask.srcs(List.is_empty(&2, U.Swap, _), rs), old2, dd2, tt2)) : List<&2, Up.Ask>}
  asks_ignore(Up.text.said(rs, Up.Ignore{}),
    Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd1)), rs), old1, old2, dd1, dd2, tt1, tt2)

law asks_asks:
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for +dd1: Up.Deps
  for +dd2: Up.Deps
  for +tt1: Up.Tools
  for +tt2: Up.Tools
  for e: {Up.deps.edits(dd1) == Up.deps.edits(dd2) : List<&2, U.Swap>}
  {Up.next.asks(Up.pins.asks(asks, rs, old1, dd1, tt1))
    == Up.next.asks(Up.pins.asks(asks, rs, old2, dd2, tt2)) : List<&2, Up.Ask>}

def asks_asks(asks, rs, old1, old2, dd1, dd2, tt1, tt2, e):
  match asks:
    case []:
      asks_settled(rs, old1, old2, dd1, dd2, tt1, tt2, e)
    case _h <> _t:
      {==}

law asks_bad:
  for clean: Bool
  for bad1: String
  for bad2: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for +dd1: Up.Deps
  for +dd2: Up.Deps
  for +tt1: Up.Tools
  for +tt2: Up.Tools
  for e: {Up.deps.edits(dd1) == Up.deps.edits(dd2) : List<&2, U.Swap>}
  {Up.next.asks(Up.pins.bad(clean, bad1, asks, rs, old1, dd1, tt1))
    == Up.next.asks(Up.pins.bad(clean, bad2, asks, rs, old2, dd2, tt2)) : List<&2, Up.Ask>}

def asks_bad(clean, _bad1, _bad2, asks, rs, old1, old2, dd1, dd2, tt1, tt2, e):
  match clean:
    case True{}:
      asks_asks(asks, rs, old1, old2, dd1, dd2, tt1, tt2, e)
    case False{}:
      {==}

# LAW: the questions after the walks are read off their keys
law pins_key:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  {Up.next.asks(Up.pins(dd, tt, rs, old1)) == Up.next.asks(Up.pins(dkey(dd), tkey(tt), rs, old2))
    : List<&2, Up.Ask>}

def pins_key(dd, tt, rs, old1, old2):
  match dd:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad}:
      match tt:
        case Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
          asks_bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            List.append(&2, Up.Ask, das, tas), rs, old1, old2,
            Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Deps{[], [], es, False{}, [], [], [], ""},
            Up.Tools{ts, tm, tsy, [], ""}, Up.Tools{[], False{}, [], [], ""}, {==})

law pins_cong:
  for +k1: Up.Deps
  for +k2: Up.Deps
  for +t1: Up.Tools
  for +t2: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old: M.Manifest
  for ek: {k1 == k2 : Up.Deps}
  for et: {t1 == t2 : Up.Tools}
  {Up.next.asks(Up.pins(k1, t1, rs, old)) == Up.next.asks(Up.pins(k2, t2, rs, old)) : List<&2, Up.Ask>}

def pins_cong(k1, _k2, t1, t2, rs, old, ek, et):
  %ek : {Up.next.asks(Up.pins(k1, t1, rs, old)) == Up.next.asks(Up.pins(_, t2, rs, old))
    : List<&2, Up.Ask>}
  %et : {Up.next.asks(Up.pins(k1, t1, rs, old)) == Up.next.asks(Up.pins(k1, _, rs, old))
    : List<&2, Up.Ask>}
  {==}

# LAW: two pairs of walks with the same keys ask the same questions, whatever
# ledgers they came from
law asks_pins:
  for +dd1: Up.Deps
  for +tt1: Up.Tools
  for +dd2: Up.Deps
  for +tt2: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +old1: M.Manifest
  for +old2: M.Manifest
  for ed: {dkey(dd1) == dkey(dd2) : Up.Deps}
  for et: {tkey(tt1) == tkey(tt2) : Up.Tools}
  {Up.next.asks(Up.pins(dd1, tt1, rs, old1)) == Up.next.asks(Up.pins(dd2, tt2, rs, old2))
    : List<&2, Up.Ask>}

def asks_pins(dd1, tt1, dd2, tt2, rs, old1, old2, ed, et):
  Equal.trans(List<&2, Up.Ask>,
    Up.next.asks(Up.pins(dd1, tt1, rs, old1)),
    Up.next.asks(Up.pins(dkey(dd1), tkey(tt1), rs, old1)),
    Up.next.asks(Up.pins(dd2, tt2, rs, old2)),
    pins_key(dd1, tt1, rs, old1, old1),
    Equal.trans(List<&2, Up.Ask>,
      Up.next.asks(Up.pins(dkey(dd1), tkey(tt1), rs, old1)),
      Up.next.asks(Up.pins(dkey(dd2), tkey(tt2), rs, old1)),
      Up.next.asks(Up.pins(dd2, tt2, rs, old2)),
      pins_cong(dkey(dd1), dkey(dd2), tkey(tt1), tkey(tt2), rs, old1, ed, et),
      Equal.sym(List<&2, Up.Ask>, Up.next.asks(Up.pins(dd2, tt2, rs, old2)),
        Up.next.asks(Up.pins(dkey(dd2), tkey(tt2), rs, old1)),
        pins_key(dd2, tt2, rs, old2, old1))))

law asks_known:
  for ok: Bool
  for +n: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {Up.next.asks(Up.known(ok, n, rs, M.Manifest{pn, pe, pb, hb, ods, ots}))
    == Up.next.asks(Up.known(ok, n, rs,
      M.Manifest{pn, pe, pb, hb, Laws.deps.named(ods, n), Laws.tools.named(ots, n)}))
    : List<&2, Up.Ask>}

def asks_known(ok, n, rs, pn, pe, pb, hb, ods, ots, ne):
  match ok:
    case False{}:
      {==}
    case True{}:
      asks_pins(Up.deps.walk(rs, n, M.hub.or(hb), ods), Up.tools.walk(rs, n, ots),
        Up.deps.walk(rs, n, M.hub.or(hb), Laws.deps.named(ods, n)),
        Up.tools.walk(rs, n, Laws.tools.named(ots, n)), rs,
        M.Manifest{pn, pe, pb, hb, ods, ots},
        M.Manifest{pn, pe, pb, hb, Laws.deps.named(ods, n), Laws.tools.named(ots, n)},
        dalone_walk(rs, n, M.hub.or(hb), ods, ne), talone_walk(rs, n, ots, ne))

# LAW: an upgrade of a ledger asks what an upgrade of its entries named `n`
# alone asks
law asks_next:
  for +n: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +ne: {String.is_empty(n) == False{} : Bool}
  {Up.next.asks(Up.next(n, r, rs)) == Up.next.asks(Up.next(n, Laws.alone(r, n), rs))
    : List<&2, Up.Ask>}

def asks_next(n, r, rs, ne):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{mm}:
      match mm:
        case M.Manifest{+pn, +pe, +pb, +hb, +ods, +ots}:
          dk = dknown(n, ods, ne)
          %dk : {Up.next.asks(Up.known(Bool.or(U.known(n, ods), M.tool.known(n, ots)), n, rs,
            M.Manifest{pn, pe, pb, hb, ods, ots}))
            == Up.next.asks(Up.known(Bool.or(_, M.tool.known(n, Laws.tools.named(ots, n))), n, rs,
              M.Manifest{pn, pe, pb, hb, Laws.deps.named(ods, n), Laws.tools.named(ots, n)}))
            : List<&2, Up.Ask>}
          tk = tknown(n, ots, ne)
          %tk : {Up.next.asks(Up.known(Bool.or(U.known(n, ods), M.tool.known(n, ots)), n, rs,
            M.Manifest{pn, pe, pb, hb, ods, ots}))
            == Up.next.asks(Up.known(Bool.or(U.known(n, ods), _), n, rs,
              M.Manifest{pn, pe, pb, hb, Laws.deps.named(ods, n), Laws.tools.named(ots, n)}))
            : List<&2, Up.Ask>}
          asks_known(Bool.or(U.known(n, ods), M.tool.known(n, ots)), n, rs, pn, pe, pb, hb, ods, ots,
            ne)

def Laws.upgrade_one_asks_alone(w, n, u, e, ne):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.wants.up(W.World{W.Args{False{}, only}, ledger, listing,
                replies, ups}) == Up.next.asks(Up.next(n, Laws.alone(W.parsed(ledger), n),
                Laws.ups.of(W.World{W.Args{False{}, only}, ledger, listing, replies, ups})))
                : List<&2, Up.Ask>}, u)
            case True{}:
              es = Equal.sym(String, only, n, e)
              %es : {Up.next.asks(Up.next(_, W.parsed(ledger), ups))
                == Up.next.asks(Up.next(n, Laws.alone(W.parsed(ledger), n), ups)) : List<&2, Up.Ask>}
              asks_next(n, W.parsed(ledger), ups, ne)
