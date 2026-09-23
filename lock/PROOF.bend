# lock: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import ./up.bend as Up
import ../manifest/manifest.bend as M
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../check/toml.bend as Toml
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

# The lock document's first step: a quoted value is its own trim, and its
# quotes strip off. Both are check/toml.bend's, for any value.
def Laws.trim_quoted(v):
  Toml.trim_ends('"', v, '"', {==}, {==})

def Laws.strip_quoted(v):
  Toml.unquote(v)

# What the lock may hold. A path holding `=` makes its package's `paths.ok`
# False, and an `and` with a False half is False whichever side it is on.

# LAW: an `and` whose right half is False is False
law and_false:
  for a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.path_eq_unlockable(hash, src, at, sum, fs, rest, ts, hub, e):
  %e : {Bool.and(P.clean(hub), Bool.and(Bool.and(Bool.and(Bool.and(_,
    P.paths.ok(fs)), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src,
    K.File{at, sum} <> fs})), Bool.not(L.has(rest, hash)))), P.packs.ok(rest)),
    P.tools.ok(ts))) == False{} : Bool}
  and_false(P.clean(hub))

# LAW: a path that holds `=` is not empty
law eqless_filled:
  for +at: String
  for e: {False{} == P.path.eqless(at) : Bool}
  {False{} == String.is_empty(at) : Bool}

def eqless_filled(at, e):
  match at:
    case SNil{}:
      Eq.bit.absurd(&2, {False{} == String.is_empty(SNil{}) : Bool}, e)
    case SCon{h, t}:
      {==}

# the reason a lock that is not lockable gives, from the scan's answer
def named.why(+why: String) -> String:
  P.lockable.pick(String.is_empty(why), why)

# The first path the scan finds is the one given, and it is not empty, so
# the reason is the one that names it.
def Laws.path_eq_named(hash, _src, at, _sum, fs, rest, e):
  f = eqless_filled(at, e)
  %e : {named.why(P.packs.eq.pick(String.is_empty(P.path.eq.pick(_, at,
    P.path.eq.first(fs))), hash, P.path.eq.pick(_, at, P.path.eq.first(fs)),
    P.packs.eq(rest))) == P.path.eq.why(hash, at) : String}
  %f : {named.why(P.packs.eq.pick(_, hash, at, P.packs.eq(rest)))
    == P.path.eq.why(hash, at) : String}
  {==}

# The lock document reads back (EZ-DOC-1). check/toml.bend proves that a
# document of tables the reader can take back parses back as those tables;
# what is left is the lock's side: that its text is such a document, that
# `lockable` makes every name and key one the reader takes back, and that
# ez's readers find what was written.

# LAW: a path the planner lets through holds no `=`
law eqless_clear:
  for +s: String
  for +e: {P.path.eqless(s) == True{} : Bool}
  {Str.clear(s, '=') == True{} : Bool}

def eqless_clear(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      and_true(Bool.not(Char.is_eq(h, '=')), Str.clear(t, '='),
        Eq.and.left(Bool.not(Char.is_eq(h, '=')), P.path.eqless(t), e),
        eqless_clear(t, Eq.and.right(Bool.not(Char.is_eq(h, '=')), P.path.eqless(t), e)))

# ---------------------------------------------------------------------------
# the lock's text is the text of its document

# LAW: inserting a package's block among blocks in order is the block list of
# inserting the package, one step, with how it compares given
law blocks_ins.step:
  for +hp: String
  for +sp: L.Src
  for +fp: List<&2, K.File>
  for +hh: String
  for +sh: L.Src
  for +fh: List<&2, K.File>
  for +t: List<&2, L.Pack>
  for b: Bool
  for ih: {K.file.ins(L.pack.blocks(t), L.pack.block(L.Pack{hp, sp, fp}))
    == L.pack.blocks(L.pack.ins(t, L.Pack{hp, sp, fp})) : List<&2, K.File>}
  {K.file.ins.put(b, L.pack.block(L.Pack{hp, sp, fp}), L.pack.block(L.Pack{hh, sh, fh}),
    L.pack.blocks(t), K.file.ins(L.pack.blocks(t), L.pack.block(L.Pack{hp, sp, fp})))
    == L.pack.blocks(L.pack.ins.put(b, L.Pack{hp, sp, fp}, L.Pack{hh, sh, fh}, t,
      L.pack.ins(t, L.Pack{hp, sp, fp}))) : List<&2, K.File>}

def blocks_ins.step(hp, sp, fp, hh, sh, fh, t, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(List<&2, K.File>, List<&2, K.File>, r => L.pack.block(L.Pack{hh, sh, fh}) <> r,
        K.file.ins(L.pack.blocks(t), L.pack.block(L.Pack{hp, sp, fp})),
        L.pack.blocks(L.pack.ins(t, L.Pack{hp, sp, fp})), ih)

# LAW: the packages compared as their blocks are compared by hash
law blocks_ins.cons:
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for +p: L.Pack
  for ih: {K.file.ins(L.pack.blocks(t), L.pack.block(p))
    == L.pack.blocks(L.pack.ins(t, p)) : List<&2, K.File>}
  {K.file.ins(L.pack.blocks(h <> t), L.pack.block(p))
    == L.pack.blocks(L.pack.ins(h <> t, p)) : List<&2, K.File>}

def blocks_ins.cons(h, t, p, ih):
  match h p:
    case L.Pack{+hh, +sh, +fh} L.Pack{+hp, +sp, +fp}:
      blocks_ins.step(hp, sp, fp, hh, sh, fh, t, String.is_le(hp, hh), ih)

# LAW: a package's block inserted among blocks in order is the blocks of the
# package inserted among packages in order
law blocks_ins:
  for +qs: List<&2, L.Pack>
  for +p: L.Pack
  {K.file.ins(L.pack.blocks(qs), L.pack.block(p)) == L.pack.blocks(L.pack.ins(qs, p))
    : List<&2, K.File>}

def blocks_ins(qs, p):
  match qs:
    case []:
      {==}
    case +h <> +t:
      blocks_ins.cons(h, t, p, blocks_ins(t, p))

# LAW: the blocks sorted are the blocks of the packages sorted
law blocks_sort:
  for +ps: List<&2, L.Pack>
  {K.file.sort(L.pack.blocks(ps)) == L.pack.blocks(L.pack.sort(ps)) : List<&2, K.File>}

def blocks_sort(ps):
  match ps:
    case []:
      {==}
    case +h <> +t:
      ih = Equal.sym(List<&2, K.File>, K.file.sort(L.pack.blocks(t)),
        L.pack.blocks(L.pack.sort(t)), blocks_sort(t))
      %ih : {K.file.ins(_, L.pack.block(h)) == L.pack.blocks(L.pack.sort(h <> t))
        : List<&2, K.File>}
      blocks_ins(L.pack.sort(t), h)

# LAW: each package's block, joined among what follows, is its two tables
# joined among it, from nothing
law blocks_join:
  for +qs: List<&2, L.Pack>
  for +rest: List<&2, String>
  {String.join.go(List.append(&2, String, L.block.texts(L.pack.blocks(qs)), rest), "", "\n")
    == String.join.go(List.append(&2, String, T.render.all(L.pack.all(qs)), rest), "", "\n")
    : String}

# one package, taken apart, with the rest's law given
law blocks_join.cons:
  for +q: L.Pack
  for +qs: List<&2, L.Pack>
  for +rest: List<&2, String>
  for ih: {String.join.go(List.append(&2, String, L.block.texts(L.pack.blocks(qs)), rest), "", "\n")
    == String.join.go(List.append(&2, String, T.render.all(L.pack.all(qs)), rest), "", "\n")
    : String}
  {String.join.go(List.append(&2, String, L.block.texts(L.pack.blocks(q <> qs)), rest), "", "\n")
    == String.join.go(List.append(&2, String, T.render.all(L.pack.all(q <> qs)), rest), "", "\n")
    : String}

def blocks_join.cons(q, qs, rest, ih):
  match q:
    case L.Pack{+hash, +src, +files}:
      +zs = List.append(&2, String, L.block.texts(L.pack.blocks(qs)), rest)
      +ys = List.append(&2, String, T.render.all(L.pack.all(qs)), rest)
      +r1 = T.render.sect(T.Sect{"packages." ++ T.quote(hash) ++ ".source", L.src.pairs(src)})
      +r2 = T.render.sect(T.Sect{"packages." ++ T.quote(hash) ++ ".files",
        L.file.pairs(K.files_of(files))})
      f1 = Equal.sym(String, String.join.go(zs, String.append(r1, SCon{'\n', r2}), "\n"),
        String.append(String.append(r1, SCon{'\n', r2}), String.join.go(zs, "", "\n")),
        Str.join_fold(zs, String.append(r1, SCon{'\n', r2})))
      f2 = Equal.sym(String, String.join.go(ys, r2, "\n"),
        String.append(r2, String.join.go(ys, "", "\n")), Str.join_fold(ys, r2))
      %f2 : {SCon{'\n', String.join.go(zs, String.append(r1, SCon{'\n', r2}), "\n")}
        == SCon{'\n', String.append(r1, SCon{'\n', _})} : String}
      %f1 : {SCon{'\n', _} == SCon{'\n', String.append(r1, SCon{'\n',
        String.append(r2, String.join.go(ys, "", "\n"))})} : String}
      %ih : {SCon{'\n', String.append(String.append(r1, SCon{'\n', r2}), String.join.go(zs, "", "\n"))}
        == SCon{'\n', String.append(r1, SCon{'\n', String.append(r2, _)})} : String}
      Equal.cong(String, String, x => SCon{'\n', x},
        String.append(String.append(r1, SCon{'\n', r2}), String.join.go(zs, "", "\n")),
        String.append(r1, SCon{'\n', String.append(r2, String.join.go(zs, "", "\n"))}),
        Eq.append_assoc(r1, SCon{'\n', r2}, String.join.go(zs, "", "\n")))

def blocks_join(qs, rest):
  match qs:
    case []:
      {==}
    case +q <> +t:
      blocks_join.cons(q, t, rest, blocks_join(t, rest))

def Laws.render_is_doc(ts, hub, ps):
  b = Equal.sym(List<&2, K.File>, K.file.sort(L.pack.blocks(ps)),
    L.pack.blocks(L.pack.sort(ps)), blocks_sort(ps))
  %b : {String.join.go(List.append(&2, String, L.block.texts(_), T.render.all(L.tool.sects(ts))),
    T.render.sect(L.lock.sect(hub)), "\n") == T.render(Laws.lock.doc(ts, hub, ps)) : String}
  ra = Equal.sym(List<&2, String>,
    T.render.all(List.append(&2, T.Sect, L.pack.all(L.pack.sort(ps)), L.tool.sects(ts))),
    List.append(&2, String, T.render.all(L.pack.all(L.pack.sort(ps))), T.render.all(L.tool.sects(ts))),
    Toml.render_all_append(L.pack.all(L.pack.sort(ps)), L.tool.sects(ts)))
  %ra : {String.join.go(List.append(&2, String, L.block.texts(L.pack.blocks(L.pack.sort(ps))),
    T.render.all(L.tool.sects(ts))), T.render.sect(L.lock.sect(hub)), "\n")
    == String.join.go(_, T.render.sect(L.lock.sect(hub)), "\n") : String}
  f1 = Equal.sym(String, String.join.go(List.append(&2, String,
      L.block.texts(L.pack.blocks(L.pack.sort(ps))), T.render.all(L.tool.sects(ts))),
      T.render.sect(L.lock.sect(hub)), "\n"),
    String.append(T.render.sect(L.lock.sect(hub)), String.join.go(List.append(&2, String,
      L.block.texts(L.pack.blocks(L.pack.sort(ps))), T.render.all(L.tool.sects(ts))), "", "\n")),
    Str.join_fold(List.append(&2, String, L.block.texts(L.pack.blocks(L.pack.sort(ps))),
      T.render.all(L.tool.sects(ts))), T.render.sect(L.lock.sect(hub))))
  %f1 : {_ == String.join.go(List.append(&2, String, T.render.all(L.pack.all(L.pack.sort(ps))),
    T.render.all(L.tool.sects(ts))), T.render.sect(L.lock.sect(hub)), "\n") : String}
  f2 = Equal.sym(String, String.join.go(List.append(&2, String,
      T.render.all(L.pack.all(L.pack.sort(ps))), T.render.all(L.tool.sects(ts))),
      T.render.sect(L.lock.sect(hub)), "\n"),
    String.append(T.render.sect(L.lock.sect(hub)), String.join.go(List.append(&2, String,
      T.render.all(L.pack.all(L.pack.sort(ps))), T.render.all(L.tool.sects(ts))), "", "\n")),
    Str.join_fold(List.append(&2, String, T.render.all(L.pack.all(L.pack.sort(ps))),
      T.render.all(L.tool.sects(ts))), T.render.sect(L.lock.sect(hub))))
  %f2 : {String.append(T.render.sect(L.lock.sect(hub)), String.join.go(List.append(&2, String,
      L.block.texts(L.pack.blocks(L.pack.sort(ps))), T.render.all(L.tool.sects(ts))), "", "\n"))
    == _ : String}
  Equal.cong(String, String, x => String.append(T.render.sect(L.lock.sect(hub)), x),
    String.join.go(List.append(&2, String, L.block.texts(L.pack.blocks(L.pack.sort(ps))),
      T.render.all(L.tool.sects(ts))), "", "\n"),
    String.join.go(List.append(&2, String, T.render.all(L.pack.all(L.pack.sort(ps))),
      T.render.all(L.tool.sects(ts))), "", "\n"),
    blocks_join(L.pack.sort(ps), T.render.all(L.tool.sects(ts))))

# LAW: and the right half
law or_right:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_right(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      Eq.bit.absurd2(&2, {b == False{} : Bool}, e)

# LAW: a string the lock can write holds no newline
law clean_nl:
  for +s: String
  for +e: {P.clean(s) == True{} : Bool}
  {Str.clear(s, '\n') == True{} : Bool}

def clean_nl(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      and_true(Bool.not(Char.is_eq(h, '\n')), Str.clear(t, '\n'),
        not_false(Char.is_eq(h, '\n'),
          or_right(Char.is_eq(h, '\\'), Char.is_eq(h, '\n'),
            or_right(Char.is_eq(h, '"'), Bool.or(Char.is_eq(h, '\\'), Char.is_eq(h, '\n')),
              Eq.not.true(P.char.bad(h),
                Eq.and.left(Bool.not(P.char.bad(h)), P.clean(t), e))))),
        clean_nl(t, Eq.and.right(Bool.not(P.char.bad(h)), P.clean(t), e)))

# LAW: and no quote
law clean_quote:
  for +s: String
  for +e: {P.clean(s) == True{} : Bool}
  {Str.clear(s, '"') == True{} : Bool}

def clean_quote(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      and_true(Bool.not(Char.is_eq(h, '"')), Str.clear(t, '"'),
        not_false(Char.is_eq(h, '"'),
          or_left(Char.is_eq(h, '"'), Bool.or(Char.is_eq(h, '\\'), Char.is_eq(h, '\n')),
            Eq.not.true(P.char.bad(h),
              Eq.and.left(Bool.not(P.char.bad(h)), P.clean(t), e)))),
        clean_quote(t, Eq.and.right(Bool.not(P.char.bad(h)), P.clean(t), e)))

# LAW: the strings before a list the lock can write, when the whole can be
law clean_all_left:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +e: {P.clean.all(List.append(&2, String, xs, ys)) == True{} : Bool}
  {P.clean.all(xs) == True{} : Bool}

def clean_all_left(xs, ys, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      and_true(P.clean(h), P.clean.all(t),
        Eq.and.left(P.clean(h), P.clean.all(List.append(&2, String, t, ys)), e),
        clean_all_left(t, ys,
          Eq.and.right(P.clean(h), P.clean.all(List.append(&2, String, t, ys)), e)))

# LAW: and the strings after them
law clean_all_right:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +e: {P.clean.all(List.append(&2, String, xs, ys)) == True{} : Bool}
  {P.clean.all(ys) == True{} : Bool}

def clean_all_right(xs, ys, e):
  match xs:
    case []:
      e
    case +h <> +t:
      clean_all_right(t, ys,
        Eq.and.right(P.clean(h), P.clean.all(List.append(&2, String, t, ys)), e))

# LAW: a pair the lock writes only when its value is not empty reads back
# with the rest, when it and the rest do
law kvs_kv:
  for +k: String
  for +v: String
  for +rest: List<&2, T.Kv>
  for ek: {Toml.kv.ok(T.Kv{k, v}) == True{} : Bool}
  for er: {Toml.kvs.ok(rest) == True{} : Bool}
  {Toml.kvs.ok(List.append(&2, T.Kv, L.kv(k, v), rest)) == True{} : Bool}

def kvs_kv(k, v, rest, ek, er):
  match v:
    case SNil{}:
      er
    case SCon{+h, +t}:
      and_true(Toml.kv.ok(T.Kv{k, SCon{h, t}}), Toml.kvs.ok(rest), ek, er)

# whether every file of a list reads back as a pair. Proof vocabulary.
def fok(fs: List<&2, K.File>) -> Bool:
  Toml.kvs.ok(L.file.pairs(fs))

# LAW: files the planner lets through read back as pairs
law files_ok:
  for +fs: List<&2, K.File>
  for +ep: {P.paths.ok(fs) == True{} : Bool}
  for +ec: {P.clean.all(P.file.values(fs)) == True{} : Bool}
  {fok(fs) == True{} : Bool}

def files_ok(fs, ep, ec):
  match fs:
    case []:
      {==}
    case K.File{+at, +sum} <> +t:
      and_true(Toml.kv.ok(T.Kv{at, sum}), fok(t),
        and_true(Str.clear(at, '='), Bool.and(Str.clear(at, '"'),
          Bool.and(Str.clear(at, '\n'), Str.clear(sum, '\n'))),
          eqless_clear(at, Eq.and.left(P.path.eqless(at), P.paths.ok(t), ep)),
          and_true(Str.clear(at, '"'), Bool.and(Str.clear(at, '\n'), Str.clear(sum, '\n')),
            clean_quote(at, Eq.and.left(P.clean(at),
              Bool.and(P.clean(sum), P.clean.all(P.file.values(t))), ec)),
            and_true(Str.clear(at, '\n'), Str.clear(sum, '\n'),
              clean_nl(at, Eq.and.left(P.clean(at),
                Bool.and(P.clean(sum), P.clean.all(P.file.values(t))), ec)),
              clean_nl(sum, Eq.and.left(P.clean(sum), P.clean.all(P.file.values(t)),
                Eq.and.right(P.clean(at),
                  Bool.and(P.clean(sum), P.clean.all(P.file.values(t))), ec)))))),
        files_ok(t, Eq.and.right(P.path.eqless(at), P.paths.ok(t), ep),
          Eq.and.right(P.clean(sum), P.clean.all(P.file.values(t)),
            Eq.and.right(P.clean(at),
              Bool.and(P.clean(sum), P.clean.all(P.file.values(t))), ec))))

# LAW: a file inserted among files that read back, when it reads back, one
# step, with how it compares given
law fins_ok.step:
  for +x: K.File
  for +h: K.File
  for +t: List<&2, K.File>
  for b: Bool
  for +ex: {fok(h <> t) == True{} : Bool}
  for +e1: {fok([x]) == True{} : Bool}
  for ih: {fok(K.file.ins(t, x)) == True{} : Bool}
  {fok(K.file.ins.put(b, x, h, t, K.file.ins(t, x))) == True{} : Bool}

def fins_ok.step(x, h, t, b, ex, e1, ih):
  match b:
    case True{}:
      and_true(Toml.kv.ok(L.file.pair(x)), fok(h <> t),
        Eq.and.left(Toml.kv.ok(L.file.pair(x)), True{}, e1), ex)
    case False{}:
      and_true(Toml.kv.ok(L.file.pair(h)), fok(K.file.ins(t, x)),
        Eq.and.left(Toml.kv.ok(L.file.pair(h)), fok(t), ex), ih)

# LAW: a file inserted among files that read back, when it reads back
law fins_ok:
  for +xs: List<&2, K.File>
  for +x: K.File
  for +ex: {fok(xs) == True{} : Bool}
  for +e1: {fok([x]) == True{} : Bool}
  {fok(K.file.ins(xs, x)) == True{} : Bool}

def fins_ok(xs, x, ex, e1):
  match xs:
    case []:
      e1
    case +h <> +t:
      fins_ok.step(x, h, t, K.file.le(x, h), ex, e1,
        fins_ok(t, x, Eq.and.right(Toml.kv.ok(L.file.pair(h)), fok(t), ex), e1))

# LAW: files that read back, sorted, read back
law fsort_ok:
  for +fs: List<&2, K.File>
  for +e: {fok(fs) == True{} : Bool}
  {fok(K.file.sort(fs)) == True{} : Bool}

def fsort_ok(fs, e):
  match fs:
    case []:
      {==}
    case +h <> +t:
      fins_ok(K.file.sort(t), h,
        fsort_ok(t, Eq.and.right(Toml.kv.ok(L.file.pair(h)), fok(t), e)),
        and_true(Toml.kv.ok(L.file.pair(h)), True{},
          Eq.and.left(Toml.kv.ok(L.file.pair(h)), fok(t), e), {==}))

# LAW: a file against deduplicated files that read back, when it reads back,
# with whether it repeats the next given
law dedup_ok.pick:
  for +h: K.File
  for +b: K.File
  for +t: List<&2, K.File>
  for same: Bool
  for +eh: {Toml.kv.ok(L.file.pair(h)) == True{} : Bool}
  for +er: {fok(b <> t) == True{} : Bool}
  {fok(K.dedup.pick(same, h, b <> t)) == True{} : Bool}

def dedup_ok.pick(h, b, t, same, eh, er):
  match same:
    case True{}:
      er
    case False{}:
      and_true(Toml.kv.ok(L.file.pair(h)), fok(b <> t), eh, er)

# LAW: and one step of the deduplication
law dedup_ok.head:
  for +h: K.File
  for +r: List<&2, K.File>
  for +eh: {Toml.kv.ok(L.file.pair(h)) == True{} : Bool}
  for +er: {fok(r) == True{} : Bool}
  {fok(K.dedup.head(h, r)) == True{} : Bool}

def dedup_ok.head(h, r, eh, er):
  match r:
    case []:
      and_true(Toml.kv.ok(L.file.pair(h)), True{}, eh, {==})
    case +b <> +t:
      dedup_ok.pick(h, b, t, String.eq(K.file.at(h), K.file.at(b)), eh, er)

# LAW: files that read back, deduplicated, read back
law dedup_ok:
  for +fs: List<&2, K.File>
  for +e: {fok(fs) == True{} : Bool}
  {fok(K.dedup(fs)) == True{} : Bool}

def dedup_ok(fs, e):
  match fs:
    case []:
      {==}
    case +h <> +t:
      dedup_ok.head(h, K.dedup(t), Eq.and.left(Toml.kv.ok(L.file.pair(h)), fok(t), e),
        dedup_ok(t, Eq.and.right(Toml.kv.ok(L.file.pair(h)), fok(t), e)))

# LAW: a package's source table reads back, when its values can be written
law src_ok:
  for +src: L.Src
  for +e: {P.clean.all(P.src.values(src)) == True{} : Bool}
  {Toml.kvs.ok(L.src.pairs(src)) == True{} : Bool}

def src_ok(src, e):
  match src:
    case L.Hub{}:
      {==}
    case L.Git{+url, +rev, +entry, +root, +nar, +tag}:
      +e1 = Eq.and.right(P.clean(url), P.clean.all([rev, entry, root, nar, tag]), e)
      +e2 = Eq.and.right(P.clean(rev), P.clean.all([entry, root, nar, tag]), e1)
      +e3 = Eq.and.right(P.clean(entry), P.clean.all([root, nar, tag]), e2)
      +e4 = Eq.and.right(P.clean(root), P.clean.all([nar, tag]), e3)
      +e5 = Eq.and.right(P.clean(nar), P.clean.all([tag]), e4)
      kvs_kv("url", url, List.concat(&2, T.Kv, [L.kv("rev", rev), L.kv("entry", entry),
          L.kv("root", root), L.kv("narHash", nar), L.kv("tag", tag)]),
        clean_nl(url, Eq.and.left(P.clean(url), P.clean.all([rev, entry, root, nar, tag]), e)),
        kvs_kv("rev", rev, List.concat(&2, T.Kv, [L.kv("entry", entry),
            L.kv("root", root), L.kv("narHash", nar), L.kv("tag", tag)]),
          clean_nl(rev, Eq.and.left(P.clean(rev), P.clean.all([entry, root, nar, tag]),
            Eq.and.right(P.clean(url), P.clean.all([rev, entry, root, nar, tag]), e))),
          kvs_kv("entry", entry, List.concat(&2, T.Kv, [L.kv("root", root),
              L.kv("narHash", nar), L.kv("tag", tag)]),
            clean_nl(entry, Eq.and.left(P.clean(entry), P.clean.all([root, nar, tag]),
              Eq.and.right(P.clean(rev), P.clean.all([entry, root, nar, tag]),
                Eq.and.right(P.clean(url), P.clean.all([rev, entry, root, nar, tag]), e)))),
            kvs_kv("root", root, List.concat(&2, T.Kv, [L.kv("narHash", nar), L.kv("tag", tag)]),
              clean_nl(root, Eq.and.left(P.clean(root), P.clean.all([nar, tag]), e3)),
              kvs_kv("narHash", nar, List.concat(&2, T.Kv, [L.kv("tag", tag)]),
                clean_nl(nar, Eq.and.left(P.clean(nar), P.clean.all([tag]), e4)),
                kvs_kv("tag", tag, [],
                  clean_nl(tag, Eq.and.left(P.clean(tag), True{}, e5)), {==}))))))

# LAW: a package's two tables read back, when the planner lets it through
law pack_ok:
  for +hash: String
  for +src: L.Src
  for +fs: List<&2, K.File>
  for +ep: {P.paths.ok(fs) == True{} : Bool}
  for +ev: {P.clean.all(hash <> List.append(&2, String, P.src.values(src), P.file.values(fs)))
    == True{} : Bool}
  {Toml.sects.ok(L.pack.sects(L.Pack{hash, src, fs})) == True{} : Bool}

def pack_ok(hash, src, fs, ep, ev):
  +eh = Eq.and.left(P.clean(hash),
    P.clean.all(List.append(&2, String, P.src.values(src), P.file.values(fs))), ev)
  +er = Eq.and.right(P.clean(hash),
    P.clean.all(List.append(&2, String, P.src.values(src), P.file.values(fs))), ev)
  +hn = clean_nl(hash, eh)
  and_true(
    Toml.sect.ok(T.Sect{"packages." ++ T.quote(hash) ++ ".source", L.src.pairs(src)}),
    Bool.and(Toml.sect.ok(T.Sect{"packages." ++ T.quote(hash) ++ ".files",
      L.file.pairs(K.files_of(fs))}), True{}),
    and_true(Str.clear(String.append(String.append(hash, "\""), ".source"), '\n'),
      Toml.kvs.ok(L.src.pairs(src)),
      Str.clear_append(String.append(hash, "\""), ".source", '\n',
        Str.clear_append(hash, "\"", '\n', hn, {==}), {==}),
      src_ok(src, clean_all_left(P.src.values(src), P.file.values(fs), er))),
    and_true(Toml.sect.ok(T.Sect{"packages." ++ T.quote(hash) ++ ".files",
        L.file.pairs(K.files_of(fs))}), True{},
      and_true(Str.clear(String.append(String.append(hash, "\""), ".files"), '\n'),
        fok(K.files_of(fs)),
        Str.clear_append(String.append(hash, "\""), ".files", '\n',
          Str.clear_append(hash, "\"", '\n', hn, {==}), {==}),
        dedup_ok(K.file.sort(fs), fsort_ok(fs,
          files_ok(fs, ep, clean_all_right(P.src.values(src), P.file.values(fs), er))))),
      {==}))

# LAW: every package the planner lets through writes tables that read back,
# one package, taken apart
law packs_ok.cons:
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for +e: {P.packs.ok(h <> t) == True{} : Bool}
  for ih: {Toml.sects.ok(L.pack.all(t)) == True{} : Bool}
  {Toml.sects.ok(L.pack.all(h <> t)) == True{} : Bool}

def packs_ok.cons(h, t, e, ih):
  match h:
    case L.Pack{+hash, +src, +fs}:
      +ok = Eq.and.left(Bool.and(P.paths.ok(fs), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src, fs})),
          Bool.not(L.has(t, hash)))), P.packs.ok(t), e)
      Toml.sects_ok_append(L.pack.sects(L.Pack{hash, src, fs}), L.pack.all(t),
        pack_ok(hash, src, fs,
          Eq.and.left(P.paths.ok(fs), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src, fs})),
            Bool.not(L.has(t, hash))), ok),
          Eq.and.left(P.clean.all(P.pack.values(L.Pack{hash, src, fs})), Bool.not(L.has(t, hash)),
            Eq.and.right(P.paths.ok(fs), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src, fs})),
              Bool.not(L.has(t, hash))), ok))),
        ih)

# LAW: every package the planner lets through writes tables that read back
law packs_ok:
  for +ps: List<&2, L.Pack>
  for +e: {P.packs.ok(ps) == True{} : Bool}
  {Toml.sects.ok(L.pack.all(ps)) == True{} : Bool}

def packs_ok(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      packs_ok.cons(h, t, e, packs_ok(t, Eq.and.right(
        Bool.and(P.paths.ok(L.pack.files(h)), Bool.and(P.clean.all(P.pack.values(h)),
          Bool.not(L.has(t, L.pack.hash(h))))), P.packs.ok(t), e)))

# LAW: a package inserted among packages whose tables read back, when its own
# do, one step, with how it compares given
law pins_ok.step:
  for +p: L.Pack
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for b: Bool
  for +eq: {Toml.sects.ok(L.pack.all(h <> t)) == True{} : Bool}
  for +ep: {Toml.sects.ok(L.pack.sects(p)) == True{} : Bool}
  for ih: {Toml.sects.ok(L.pack.all(L.pack.ins(t, p))) == True{} : Bool}
  {Toml.sects.ok(L.pack.all(L.pack.ins.put(b, p, h, t, L.pack.ins(t, p)))) == True{} : Bool}

def pins_ok.step(p, h, t, b, eq, ep, ih):
  match b:
    case True{}:
      Toml.sects_ok_append(L.pack.sects(p), L.pack.all(h <> t), ep, eq)
    case False{}:
      Toml.sects_ok_append(L.pack.sects(h), L.pack.all(L.pack.ins(t, p)),
        Toml.sects_ok_left(L.pack.sects(h), L.pack.all(t), eq), ih)

# LAW: a package inserted among packages whose tables read back, when its own
# do
law pins_ok:
  for +qs: List<&2, L.Pack>
  for +p: L.Pack
  for +eq: {Toml.sects.ok(L.pack.all(qs)) == True{} : Bool}
  for +ep: {Toml.sects.ok(L.pack.sects(p)) == True{} : Bool}
  {Toml.sects.ok(L.pack.all(L.pack.ins(qs, p))) == True{} : Bool}

def pins_ok(qs, p, eq, ep):
  match qs:
    case []:
      Toml.sects_ok_append(L.pack.sects(p), [], ep, {==})
    case +h <> +t:
      pins_ok.step(p, h, t, L.pack.le(p, h), eq, ep,
        pins_ok(t, p, Toml.sects_ok_right(L.pack.sects(h), L.pack.all(t), eq), ep))

# LAW: packages whose tables read back, sorted, still do
law psort_ok:
  for +ps: List<&2, L.Pack>
  for +e: {Toml.sects.ok(L.pack.all(ps)) == True{} : Bool}
  {Toml.sects.ok(L.pack.all(L.pack.sort(ps))) == True{} : Bool}

def psort_ok(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      pins_ok(L.pack.sort(t), h,
        psort_ok(t, Toml.sects_ok_right(L.pack.sects(h), L.pack.all(t), e)),
        Toml.sects_ok_left(L.pack.sects(h), L.pack.all(t), e))

# LAW: a tool's table reads back, when the planner lets its pin through, with
# its source taken apart
law tool_ok.src:
  for +n: String
  for +e: String
  for +b: String
  for +s: M.Source
  for +ev: {P.clean.all(P.tool.values(M.Tool{n, e, b, s})) == True{} : Bool}
  {Toml.sect.ok(L.tool.sect(M.Tool{n, e, b, s})) == True{} : Bool}

def tool_ok.src(n, e, b, s, ev):
  match s:
    case M.Hub{}:
      +e1 = Eq.and.right(P.clean(n), P.clean.all([e, b]), ev)
      and_true(Str.clear(n, '\n'),
        Toml.kvs.ok(List.concat(&2, T.Kv, [L.kv("entry", e), L.kv("bin", b)])),
        clean_nl(n, Eq.and.left(P.clean(n), P.clean.all([e, b]), ev)),
        kvs_kv("entry", e, List.concat(&2, T.Kv, [L.kv("bin", b)]),
          clean_nl(e, Eq.and.left(P.clean(e), P.clean.all([b]), e1)),
          kvs_kv("bin", b, [],
            clean_nl(b, Eq.and.left(P.clean(b), True{},
              Eq.and.right(P.clean(e), P.clean.all([b]), e1))), {==})))
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +e1 = Eq.and.right(P.clean(n), P.clean.all([e, b, url, rev, tag, root, nar]), ev)
      +e2 = Eq.and.right(P.clean(e), P.clean.all([b, url, rev, tag, root, nar]), e1)
      +e3 = Eq.and.right(P.clean(b), P.clean.all([url, rev, tag, root, nar]), e2)
      +e4 = Eq.and.right(P.clean(url), P.clean.all([rev, tag, root, nar]), e3)
      +e5 = Eq.and.right(P.clean(rev), P.clean.all([tag, root, nar]), e4)
      +e6 = Eq.and.right(P.clean(tag), P.clean.all([root, nar]), e5)
      +e7 = Eq.and.right(P.clean(root), P.clean.all([nar]), e6)
      and_true(Str.clear(n, '\n'),
        Toml.kvs.ok(List.concat(&2, T.Kv, [L.kv("git", url), L.kv("rev", rev), L.kv("tag", tag),
          L.kv("root", root), L.kv("narHash", nar), L.kv("entry", e), L.kv("bin", b)])),
        clean_nl(n, Eq.and.left(P.clean(n), P.clean.all([e, b, url, rev, tag, root, nar]), ev)),
        kvs_kv("git", url, List.concat(&2, T.Kv, [L.kv("rev", rev), L.kv("tag", tag),
            L.kv("root", root), L.kv("narHash", nar), L.kv("entry", e), L.kv("bin", b)]),
          clean_nl(url, Eq.and.left(P.clean(url), P.clean.all([rev, tag, root, nar]), e3)),
        kvs_kv("rev", rev, List.concat(&2, T.Kv, [L.kv("tag", tag),
            L.kv("root", root), L.kv("narHash", nar), L.kv("entry", e), L.kv("bin", b)]),
          clean_nl(rev, Eq.and.left(P.clean(rev), P.clean.all([tag, root, nar]), e4)),
        kvs_kv("tag", tag, List.concat(&2, T.Kv, [L.kv("root", root), L.kv("narHash", nar),
            L.kv("entry", e), L.kv("bin", b)]),
          clean_nl(tag, Eq.and.left(P.clean(tag), P.clean.all([root, nar]), e5)),
        kvs_kv("root", root, List.concat(&2, T.Kv, [L.kv("narHash", nar),
            L.kv("entry", e), L.kv("bin", b)]),
          clean_nl(root, Eq.and.left(P.clean(root), P.clean.all([nar]), e6)),
        kvs_kv("narHash", nar, List.concat(&2, T.Kv, [L.kv("entry", e), L.kv("bin", b)]),
          clean_nl(nar, Eq.and.left(P.clean(nar), True{}, e7)),
        kvs_kv("entry", e, List.concat(&2, T.Kv, [L.kv("bin", b)]),
          clean_nl(e, Eq.and.left(P.clean(e), P.clean.all([b, url, rev, tag, root, nar]), e1)),
        kvs_kv("bin", b, [],
          clean_nl(b, Eq.and.left(P.clean(b), P.clean.all([url, rev, tag, root, nar]), e2)),
          {==}))))))))

# LAW: a tool's table reads back, when the planner lets its pin through
law tool_ok:
  for +tool: M.Tool
  for +ev: {P.clean.all(P.tool.values(tool)) == True{} : Bool}
  {Toml.sect.ok(L.tool.sect(tool)) == True{} : Bool}

def tool_ok(tool, ev):
  match tool:
    case M.Tool{+n, +e, +b, +s}:
      tool_ok.src(n, e, b, s, ev)

# LAW: every tool's table reads back, when the planner lets every pin through
law tools_ok:
  for +ts: List<&2, M.Tool>
  for +e: {P.tools.ok(ts) == True{} : Bool}
  {Toml.sects.ok(L.tool.sects(ts)) == True{} : Bool}

def tools_ok(ts, e):
  match ts:
    case []:
      {==}
    case +h <> +t:
      and_true(Toml.sect.ok(L.tool.sect(h)), Toml.sects.ok(L.tool.sects(t)),
        tool_ok(h, Eq.and.left(P.clean.all(P.tool.values(h)), P.tools.ok(t), e)),
        tools_ok(t, Eq.and.right(P.clean.all(P.tool.values(h)), P.tools.ok(t), e)))

# LAW: the document of a lock the planner lets through reads back
law doc_ok:
  for +ps: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for +e: {P.lockable(ps, ts, hub) == True{} : Bool}
  {Toml.sects.ok(Laws.lock.doc(ts, hub, ps)) == True{} : Bool}

def doc_ok(ps, ts, hub, e):
  +er = Eq.and.right(P.clean(hub), Bool.and(P.packs.ok(ps), P.tools.ok(ts)), e)
  and_true(Toml.sect.ok(L.lock.sect(hub)),
    Toml.sects.ok(List.append(&2, T.Sect, L.pack.all(L.pack.sort(ps)), L.tool.sects(ts))),
    and_true(Str.clear(hub, '\n'), True{},
      clean_nl(hub, Eq.and.left(P.clean(hub), Bool.and(P.packs.ok(ps), P.tools.ok(ts)), e)),
      {==}),
    Toml.sects_ok_append(L.pack.all(L.pack.sort(ps)), L.tool.sects(ts),
      psort_ok(ps, packs_ok(ps, Eq.and.left(P.packs.ok(ps), P.tools.ok(ts), er))),
      tools_ok(ts, Eq.and.right(P.packs.ok(ps), P.tools.ok(ts), er))))

def Laws.lock_sections_read_back(ps, ts, hub, ok):
  r = Equal.sym(String, L.render.tools(ts, hub, ps), T.render(Laws.lock.doc(ts, hub, ps)),
    Laws.render_is_doc(ts, hub, ps))
  %r : {T.sects(T.parse(_)) == Laws.lock.doc(ts, hub, ps) : List<&2, T.Sect>}
  Toml.sections_read(L.lock.sect(hub),
    List.append(&2, T.Sect, L.pack.all(L.pack.sort(ps)), L.tool.sects(ts)),
    doc_ok(ps, ts, hub, ok))

# the header of one of a package's tables. Proof vocabulary.
def pack.name(h: String, x: String) -> String:
  "packages." ++ T.quote(h) ++ SCon{'.', x}

# LAW: a package table's header is three segments: `packages`, the hash and
# the table's own name, when the hash holds no quote and the name no quote
# and no dot
law seg_pack:
  for +h: String
  for +x: String
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  for +eq: {Str.clear(x, '"') == True{} : Bool}
  for +ed: {Str.clear(x, '.') == True{} : Bool}
  {T.segments(pack.name(h, x)) == ["packages", h, x] : List<&2, String>}

def seg_pack(h, x, eh, eq, ed):
  a1 = Equal.sym(List<&2, Char>,
    String.to_list(String.append(String.append(h, "\""), SCon{'.', x})),
    List.append(&2, Char, String.to_list(String.append(h, "\"")), '.' <> String.to_list(x)),
    Str.to_list_append(String.append(h, "\""), SCon{'.', x}))
  %a1 : {T.seg.fin(T.seg.walk(_, T.Split{True{}, [], ["packages"]})) == ["packages", h, x]
    : List<&2, String>}
  a2 = Equal.sym(List<&2, Char>, String.to_list(String.append(h, "\"")),
    List.append(&2, Char, String.to_list(h), ['"']), Str.to_list_append(h, "\""))
  %a2 : {T.seg.fin(T.seg.walk(List.append(&2, Char, _, '.' <> String.to_list(x)),
    T.Split{True{}, [], ["packages"]})) == ["packages", h, x] : List<&2, String>}
  a3 = Equal.sym(List<&2, Char>,
    List.append(&2, Char, List.append(&2, Char, String.to_list(h), ['"']), '.' <> String.to_list(x)),
    List.append(&2, Char, String.to_list(h), '"' <> '.' <> String.to_list(x)),
    Str.list_append_assoc(Char, String.to_list(h), ['"'], '.' <> String.to_list(x)))
  %a3 : {T.seg.fin(T.seg.walk(_, T.Split{True{}, [], ["packages"]})) == ["packages", h, x]
    : List<&2, String>}
  a4 = Equal.sym(T.Split,
    T.seg.walk(List.append(&2, Char, String.to_list(h), '"' <> '.' <> String.to_list(x)),
      T.Split{True{}, [], ["packages"]}),
    T.seg.walk('"' <> '.' <> String.to_list(x),
      T.seg.walk(String.to_list(h), T.Split{True{}, [], ["packages"]})),
    Toml.seg_walk_append(String.to_list(h), '"' <> '.' <> String.to_list(x), T.Split{True{}, [], ["packages"]}))
  %a4 : {T.seg.fin(_) == ["packages", h, x] : List<&2, String>}
  a5 = Equal.sym(T.Split, T.seg.walk(String.to_list(h), T.Split{True{}, [], ["packages"]}),
    T.Split{True{}, List.reverse.go(&2, Char, String.to_list(h), []), ["packages"]},
    Toml.seg_quoted(h, [], ["packages"], eh))
  %a5 : {T.seg.fin(T.seg.walk('"' <> '.' <> String.to_list(x), _)) == ["packages", h, x]
    : List<&2, String>}
  a6 = Equal.sym(T.Split,
    T.seg.walk(String.to_list(x), T.Split{False{}, [],
      [T.seg.done(List.reverse.go(&2, Char, String.to_list(h), [])), "packages"]}),
    T.Split{False{}, List.reverse.go(&2, Char, String.to_list(x), []),
      [T.seg.done(List.reverse.go(&2, Char, String.to_list(h), [])), "packages"]},
    Toml.seg_plain(x, [], [T.seg.done(List.reverse.go(&2, Char, String.to_list(h), [])), "packages"],
      eq, ed))
  %a6 : {T.seg.fin(_) == ["packages", h, x] : List<&2, String>}
  b1 = Equal.sym(String, T.seg.done(List.reverse.go(&2, Char, String.to_list(h), [])), h,
    Toml.seg_done_rev(h))
  b2 = Equal.sym(String, T.seg.done(List.reverse.go(&2, Char, String.to_list(x), [])), x,
    Toml.seg_done_rev(x))
  %b1 : {["packages", _, T.seg.done(List.reverse.go(&2, Char, String.to_list(x), []))]
    == ["packages", h, x] : List<&2, String>}
  %b2 : {["packages", h, _] == ["packages", h, x] : List<&2, String>}
  {==}

# LAW: the first segment of a walk that had one segment behind it is that one
law fin_frame:
  for +st: T.Split
  for +x: String
  {K.word(T.seg.fin(Toml.seg.frame(st, [x])), 0n) == x : String}

def fin_frame(st, x):
  match st:
    case T.Split{+q, +cur, +o}:
      r = Equal.sym(List<&2, String>,
        List.reverse.go(&2, String, List.append(&2, String, o, [x]), [T.seg.done(cur)]),
        x <> List.reverse.go(&2, String, o, [T.seg.done(cur)]),
        Str.list_rev_last(String, o, x, [T.seg.done(cur)]))
      %r : {K.word(_, 0n) == x : String}
      {==}

# LAW: a tool table's header starts with `tools`, whatever the tool is named
law seg_tools:
  for +n: String
  {K.word(T.segments("tools." ++ n), 0n) == "tools" : String}

def seg_tools(n):
  f = Equal.sym(T.Split,
    T.seg.walk(String.to_list(n), Toml.seg.frame(T.Split{False{}, [], []}, ["tools"])),
    Toml.seg.frame(T.seg.walk(String.to_list(n), T.Split{False{}, [], []}), ["tools"]),
    Toml.walk_frame(String.to_list(n), T.Split{False{}, [], []}, ["tools"]))
  %f : {K.word(T.seg.fin(_), 0n) == "tools" : String}
  fin_frame(T.seg.walk(String.to_list(n), T.Split{False{}, [], []}), "tools")

# ---------------------------------------------------------------------------
# the values a table's pairs give back

# The values a table's pairs give back. A source or a tool is written as a
# run of pairs with distinct keys, a pair left out when its value is empty.
# A lookup reads such a run as it reads the run with every pair written,
# empty values included, and over that run a lookup for a key the text names
# computes.

# the run of pairs keys and values are written as, a pair left out when its
# value is empty. Proof vocabulary.
def kvs.of(ks: List<&2, String>, vs: List<&2, String>) -> List<&2, T.Kv>:
  match ks vs:
    case Nil{} _:
      []
    case Con{_k, _kt} Nil{}:
      []
    case Con{k, kt} Con{v, vt}:
      List.append(&2, T.Kv, L.kv(k, v), kvs.of(kt, vt))

# the same run with every pair written
def full.of(ks: List<&2, String>, vs: List<&2, String>) -> List<&2, T.Kv>:
  match ks vs:
    case Nil{} _:
      []
    case Con{_k, _kt} Nil{}:
      []
    case Con{k, kt} Con{v, vt}:
      T.Kv{k, v} <> full.of(kt, vt)

# whether a key is none of the keys given
def keys.fresh(+key: String, ks: List<&2, String>) -> Bool:
  match ks:
    case []:
      True{}
    case h <> t:
      rest = keys.fresh(key, t)
      Bool.and(Bool.not(String.eq(key, h)), rest)

# whether no key is given twice
def keys.distinct(ks: List<&2, String>) -> Bool:
  match ks:
    case []:
      True{}
    case +h <> +t:
      rest = keys.distinct(t)
      Bool.and(keys.fresh(h, t), rest)

# LAW: a lookup for a key a run does not have finds nothing
law full_absent:
  for +key: String
  for +ks: List<&2, String>
  for +vs: List<&2, String>
  for +e: {keys.fresh(key, ks) == True{} : Bool}
  {T.value(full.of(ks, vs), key) == "" : String}

# by induction on the keys: none is the one looked for
def full_absent(key, ks, vs, e):
  match ks vs:
    case Nil{} _:
      {==}
    case Con{_k, _kt} Nil{}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      f = Equal.sym(Bool, String.eq(k, key), False{},
        Str.eq_flip(key, k, Eq.not.true(String.eq(key, k),
          Eq.and.left(Bool.not(String.eq(key, k)), keys.fresh(key, kt), e))))
      %f : {Bool.pick(String, _, v, T.value(full.of(kt, vt), key)) == "" : String}
      full_absent(key, kt, vt, Eq.and.right(Bool.not(String.eq(key, k)), keys.fresh(key, kt), e))

# LAW: a lookup reads a run with a pair left out when its value is empty as
# the run with every pair written, one pair, with its value and how its key
# compares given
law kvs_full.go:
  for +k: String
  for +kt: List<&2, String>
  for +v: String
  for +vt: List<&2, String>
  for +key: String
  for b: Bool
  for +eb: {String.eq(k, key) == b : Bool}
  for +ef: {keys.fresh(k, kt) == True{} : Bool}
  for ih: {T.value(kvs.of(kt, vt), key) == T.value(full.of(kt, vt), key) : String}
  {T.value(List.append(&2, T.Kv, L.kv(k, v), kvs.of(kt, vt)), key)
    == T.value(T.Kv{k, v} <> full.of(kt, vt), key) : String}

# an empty value is left out, which a lookup for another key does not see
# and a lookup for its own finds nothing where it was
def kvs_full.go(k, kt, v, vt, key, b, eb, ef, ih):
  match v b:
    case SNil{} False{}:
      f = Equal.sym(Bool, String.eq(k, key), False{}, eb)
      %f : {T.value(kvs.of(kt, vt), key) == Bool.pick(String, _, "", T.value(full.of(kt, vt), key))
        : String}
      ih
    case SNil{} True{}:
      f = Equal.sym(Bool, String.eq(k, key), True{}, eb)
      %f : {T.value(kvs.of(kt, vt), key) == Bool.pick(String, _, "", T.value(full.of(kt, vt), key))
        : String}
      Equal.trans(String, T.value(kvs.of(kt, vt), key), T.value(full.of(kt, vt), key), "", ih,
        Equal.trans(String, T.value(full.of(kt, vt), key), T.value(full.of(kt, vt), k), "",
          Equal.cong(String, String, x => T.value(full.of(kt, vt), x), key, k,
            Equal.sym(String, k, key, Str.string_eq_true(k, key, eb))),
          full_absent(k, kt, vt, ef)))
    case SCon{+h, +t} _:
      Equal.cong(String, String, x => Bool.pick(String, String.eq(k, key), SCon{h, t}, x),
        T.value(kvs.of(kt, vt), key), T.value(full.of(kt, vt), key), ih)

# LAW: a lookup reads a run with a pair left out when its value is empty as
# the run with every pair written, when no key is given twice
law kvs_full:
  for +ks: List<&2, String>
  for +vs: List<&2, String>
  for +key: String
  for +e: {keys.distinct(ks) == True{} : Bool}
  {T.value(kvs.of(ks, vs), key) == T.value(full.of(ks, vs), key) : String}

# by induction on the keys
def kvs_full(ks, vs, key, e):
  match ks vs:
    case Nil{} _:
      {==}
    case Con{_k, _kt} Nil{}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      kvs_full.go(k, kt, v, vt, key, String.eq(k, key), {==},
        Eq.and.left(keys.fresh(k, kt), keys.distinct(kt), e),
        kvs_full(kt, vt, key, Eq.and.right(keys.fresh(k, kt), keys.distinct(kt), e)))

# LAW: a package's source reads back from the pairs it is written as, with
# the source taken apart
law src_read.git:
  for +url: String
  for +rev: String
  for +entry: String
  for +root: String
  for +nar: String
  for +tag: String
  {L.src_of(L.src.pairs(L.Git{url, rev, entry, root, nar, tag}))
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}

# each value, looked up in the run with every pair written, is the value
def src_read.git(url, rev, entry, root, nar, tag):
  r0 = Equal.sym(String, T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root,
      nar, tag]), "url"),
    T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "url"),
        kvs_full(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag], "url", {==}))
  %r0 : {L.Git{_,
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "rev"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "entry"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "root"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "narHash"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "tag")}
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  r1 = Equal.sym(String, T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root,
      nar, tag]), "rev"),
    T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "rev"),
        kvs_full(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag], "rev", {==}))
  %r1 : {L.Git{T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]),
      "url"),
      _,
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "entry"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "root"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "narHash"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "tag")}
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  r2 = Equal.sym(String, T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root,
      nar, tag]), "entry"),
    T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "entry"),
        kvs_full(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag], "entry", {==}))
  %r2 : {L.Git{T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]),
      "url"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "rev"),
      _,
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "root"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "narHash"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "tag")}
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  r3 = Equal.sym(String, T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root,
      nar, tag]), "root"),
    T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "root"),
        kvs_full(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag], "root", {==}))
  %r3 : {L.Git{T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]),
      "url"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "rev"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "entry"),
      _,
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "narHash"),
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "tag")}
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  r4 = Equal.sym(String, T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root,
      nar, tag]), "narHash"),
    T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "narHash"),
        kvs_full(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag], "narHash", {==}))
  %r4 : {L.Git{T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]),
      "url"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "rev"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "entry"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "root"),
      _,
      T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "tag")}
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  r5 = Equal.sym(String, T.value(kvs.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root,
      nar, tag]), "tag"),
    T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "tag"),
        kvs_full(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag], "tag", {==}))
  %r5 : {L.Git{T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]),
      "url"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "rev"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "entry"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "root"),
      T.value(full.of(["url", "rev", "entry", "root", "narHash", "tag"], [url, rev, entry, root, nar, tag]), "narHash"),
      _}
    == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  {==}

# LAW: a package's source reads back from the pairs it is written as
law src_read:
  for +src: L.Src
  {L.src_of(L.src.pairs(src)) == src : L.Src}

def src_read(src):
  match src:
    case L.Hub{}:
      {==}
    case L.Git{+url, +rev, +entry, +root, +nar, +tag}:
      src_read.git(url, rev, entry, root, nar, tag)

# LAW: a package's files read back from the pairs they are written as
law pair_files:
  for +fs: List<&2, K.File>
  {L.pair.files(L.file.pairs(fs)) == fs : List<&2, K.File>}

def pair_files(fs):
  match fs:
    case []:
      {==}
    case K.File{+at, +sum} <> +t:
      Equal.cong(List<&2, K.File>, List<&2, K.File>, r => K.File{at, sum} <> r,
        L.pair.files(L.file.pairs(t)), t, pair_files(t))

# LAW: a git tool reads back from the pairs it is written as, as the lock
# gives it back
law tool_of.git:
  for +n: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +e: String
  for +b: String
  {M.tool_of("tools." ++ n, kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]))
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}

# the name is what follows `tools.`, and each value is looked up in the run
# with every pair written, where `vendor` is not
def tool_of.git(n, url, rev, tag, root, nar, e, b):
  d = Equal.sym(String, String.drop(n, 0n), n, Str.drop_zero(n))
  %d : {M.Tool{_, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
      e, b]), "entry"), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
          nar, e, b]), "bin"), M.source_of(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
              tag, root, nar, e, b]))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t0 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "entry"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "entry"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b],
            "entry", {==}))
  %t0 : {M.Tool{n, _, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "bin"),
      M.source.go(String.is_empty(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), T.value(kvs.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "rev"), T.value(kvs.of(["git", "rev", "tag",
                      "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
                root, nar, e, b]), "narHash"), M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry",
                    "bin"], [url, rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t1 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "bin"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "bin"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b],
            "bin", {==}))
  %t1 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), _,
      M.source.go(String.is_empty(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), T.value(kvs.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "rev"), T.value(kvs.of(["git", "rev", "tag",
                      "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
                root, nar, e, b]), "narHash"), M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry",
                    "bin"], [url, rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t2 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "git"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "git"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b],
            "git", {==}))
  %t2 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
          root, nar, e, b]), "bin"),
      M.source.go(String.is_empty(_), _, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
          [url, rev, tag, root, nar, e, b]), "rev"), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry",
              "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
                root, nar, e, b]), "narHash"), M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry",
                    "bin"], [url, rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t3 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "rev"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "rev"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b],
            "rev", {==}))
  %t3 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
          root, nar, e, b]), "bin"),
      M.source.go(String.is_empty(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), _, T.value(kvs.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
                root, nar, e, b]), "narHash"), M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry",
                    "bin"], [url, rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t4 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "tag"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "tag"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b],
            "tag", {==}))
  %t4 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
          root, nar, e, b]), "bin"),
      M.source.go(String.is_empty(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), T.value(full.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "rev"), _,
        M.root.or(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
                root, nar, e, b]), "narHash"), M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry",
                    "bin"], [url, rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t5 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "root"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "root"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b],
            "root", {==}))
  %t5 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
          root, nar, e, b]), "bin"),
      M.source.go(String.is_empty(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), T.value(full.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "rev"), T.value(full.of(["git", "rev", "tag",
                      "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(_), T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
            nar, e, b]), "narHash"), M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
                [url, rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t6 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "narHash"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "narHash"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e,
            b], "narHash", {==}))
  %t6 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
          root, nar, e, b]), "bin"),
      M.source.go(String.is_empty(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), T.value(full.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "rev"), T.value(full.of(["git", "rev", "tag",
                      "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), _, M.flag(T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url,
                rev, tag, root, nar, e, b]), "vendor")))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  t7 = Equal.sym(String, T.value(kvs.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
      root, nar, e, b]), "vendor"),
    T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]),
        "vendor"), kvs_full(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e,
            b], "vendor", {==}))
  %t7 : {M.Tool{n, T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root,
      nar, e, b]), "entry"), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag,
          root, nar, e, b]), "bin"),
      M.source.go(String.is_empty(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
          tag, root, nar, e, b]), "git")), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"],
              [url, rev, tag, root, nar, e, b]), "git"), T.value(full.of(["git", "rev", "tag", "root", "narHash",
                  "entry", "bin"], [url, rev, tag, root, nar, e, b]), "rev"), T.value(full.of(["git", "rev", "tag",
                      "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar, e, b]), "tag"),
        M.root.or(T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev, tag, root, nar,
            e, b]), "root")), T.value(full.of(["git", "rev", "tag", "root", "narHash", "entry", "bin"], [url, rev,
                tag, root, nar, e, b]), "narHash"), M.flag(_))}
    == M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})} : M.Tool}
  {==}

# LAW: a hub tool reads back from the pairs it is written as
law tool_of.hub:
  for +n: String
  for +e: String
  for +b: String
  {M.tool_of("tools." ++ n, kvs.of(["entry", "bin"], [e, b])) == M.Tool{n, e, b, M.Hub{}} : M.Tool}

# as for a git tool, with no `git` to make it one
def tool_of.hub(n, e, b):
  d = Equal.sym(String, String.drop(n, 0n), n, Str.drop_zero(n))
  %d : {M.Tool{_, T.value(kvs.of(["entry", "bin"], [e, b]), "entry"), T.value(kvs.of(["entry", "bin"], [e, b]),
      "bin"), M.source_of(kvs.of(["entry", "bin"], [e, b]))}
    == M.Tool{n, e, b, M.Hub{}} : M.Tool}
  t0 = Equal.sym(String, T.value(kvs.of(["entry", "bin"], [e, b]), "entry"),
    T.value(full.of(["entry", "bin"], [e, b]), "entry"), kvs_full(["entry", "bin"], [e, b], "entry", {==}))
  %t0 : {M.Tool{n, _, T.value(kvs.of(["entry", "bin"], [e, b]), "bin"),
      M.source.go(String.is_empty(T.value(kvs.of(["entry", "bin"], [e, b]), "git")), T.value(kvs.of(["entry", "bin"],
          [e, b]), "git"), T.value(kvs.of(["entry", "bin"], [e, b]), "rev"), T.value(kvs.of(["entry", "bin"], [e, b]),
              "tag"),
        M.root.or(T.value(kvs.of(["entry", "bin"], [e, b]), "root")), T.value(kvs.of(["entry", "bin"], [e, b]),
            "narHash"), M.flag(T.value(kvs.of(["entry", "bin"], [e, b]), "vendor")))}
    == M.Tool{n, e, b, M.Hub{}} : M.Tool}
  t1 = Equal.sym(String, T.value(kvs.of(["entry", "bin"], [e, b]), "bin"),
    T.value(full.of(["entry", "bin"], [e, b]), "bin"), kvs_full(["entry", "bin"], [e, b], "bin", {==}))
  %t1 : {M.Tool{n, T.value(full.of(["entry", "bin"], [e, b]), "entry"), _,
      M.source.go(String.is_empty(T.value(kvs.of(["entry", "bin"], [e, b]), "git")), T.value(kvs.of(["entry", "bin"],
          [e, b]), "git"), T.value(kvs.of(["entry", "bin"], [e, b]), "rev"), T.value(kvs.of(["entry", "bin"], [e, b]),
              "tag"),
        M.root.or(T.value(kvs.of(["entry", "bin"], [e, b]), "root")), T.value(kvs.of(["entry", "bin"], [e, b]),
            "narHash"), M.flag(T.value(kvs.of(["entry", "bin"], [e, b]), "vendor")))}
    == M.Tool{n, e, b, M.Hub{}} : M.Tool}
  t2 = Equal.sym(String, T.value(kvs.of(["entry", "bin"], [e, b]), "git"),
    T.value(full.of(["entry", "bin"], [e, b]), "git"), kvs_full(["entry", "bin"], [e, b], "git", {==}))
  %t2 : {M.Tool{n, T.value(full.of(["entry", "bin"], [e, b]), "entry"), T.value(full.of(["entry", "bin"], [e, b]),
      "bin"),
      M.source.go(String.is_empty(_), _, T.value(kvs.of(["entry", "bin"], [e, b]), "rev"), T.value(kvs.of(["entry",
          "bin"], [e, b]), "tag"),
        M.root.or(T.value(kvs.of(["entry", "bin"], [e, b]), "root")), T.value(kvs.of(["entry", "bin"], [e, b]),
            "narHash"), M.flag(T.value(kvs.of(["entry", "bin"], [e, b]), "vendor")))}
    == M.Tool{n, e, b, M.Hub{}} : M.Tool}
  {==}

# LAW: a tool's table, read, is the tool as the lock gives it back, with its
# source taken apart
law tools_read.src:
  for +n: String
  for +e: String
  for +b: String
  for +s: M.Source
  for +rest: List<&2, T.Sect>
  {M.tools(L.tool.sect(M.Tool{n, e, b, s}) <> rest)
    == Laws.tool.canon(M.Tool{n, e, b, s}) <> M.tools(rest) : List<&2, M.Tool>}

def tools_read.src(n, e, b, s, rest):
  match s:
    case M.Hub{}:
      f = Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
      %f : {M.tools.put(_, L.tool.sect(M.Tool{n, e, b, M.Hub{}}), M.tools(rest))
        == Laws.tool.canon(M.Tool{n, e, b, M.Hub{}}) <> M.tools(rest) : List<&2, M.Tool>}
      Equal.cong(M.Tool, List<&2, M.Tool>, x => x <> M.tools(rest),
        M.tool_of("tools." ++ n, List.concat(&2, T.Kv, [L.kv("entry", e), L.kv("bin", b)])),
        M.Tool{n, e, b, M.Hub{}}, tool_of.hub(n, e, b))
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      f = Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
      %f : {M.tools.put(_, L.tool.sect(M.Tool{n, e, b, M.Git{url, rev, tag, root, nar, vend}}), M.tools(rest))
        == Laws.tool.canon(M.Tool{n, e, b, M.Git{url, rev, tag, root, nar, vend}}) <> M.tools(rest)
        : List<&2, M.Tool>}
      Equal.cong(M.Tool, List<&2, M.Tool>, x => x <> M.tools(rest),
        M.tool_of("tools." ++ n, List.concat(&2, T.Kv, [L.kv("git", url), L.kv("rev", rev),
          L.kv("tag", tag), L.kv("root", root), L.kv("narHash", nar), L.kv("entry", e),
          L.kv("bin", b)])),
        M.Tool{n, e, b, M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, False{})},
        tool_of.git(n, url, rev, tag, root, nar, e, b))

# LAW: every tool's table, read, is the tool list as the lock gives it back
law tools_read:
  for +ts: List<&2, M.Tool>
  {M.tools(L.tool.sects(ts)) == Laws.tools.canon(ts) : List<&2, M.Tool>}

# one tool, taken apart
law tools_read.cons:
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for ih: {M.tools(L.tool.sects(t)) == Laws.tools.canon(t) : List<&2, M.Tool>}
  {M.tools(L.tool.sects(h <> t)) == Laws.tools.canon(h <> t) : List<&2, M.Tool>}

def tools_read.cons(h, t, ih):
  match h:
    case M.Tool{+n, +e, +b, +s}:
      r = tools_read.src(n, e, b, s, L.tool.sects(t))
      %ih : {M.tools(L.tool.sects(M.Tool{n, e, b, s} <> t))
        == Laws.tool.canon(M.Tool{n, e, b, s}) <> _ : List<&2, M.Tool>}
      r

def tools_read(ts):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tools_read.cons(h, t, tools_read(t))

# LAW: a package's tables are no tool's
law tools_skip_packs:
  for +qs: List<&2, L.Pack>
  for +rest: List<&2, T.Sect>
  {M.tools(List.append(&2, T.Sect, L.pack.all(qs), rest)) == M.tools(rest) : List<&2, M.Tool>}

# one package, taken apart
law tools_skip_packs.cons:
  for +q: L.Pack
  for +qs: List<&2, L.Pack>
  for +rest: List<&2, T.Sect>
  for ih: {M.tools(List.append(&2, T.Sect, L.pack.all(qs), rest)) == M.tools(rest)
    : List<&2, M.Tool>}
  {M.tools(List.append(&2, T.Sect, L.pack.all(q <> qs), rest)) == M.tools(rest)
    : List<&2, M.Tool>}

def tools_skip_packs.cons(q, _qs, _rest, ih):
  match q:
    case L.Pack{+h, +s, +f}:
      ih

def tools_skip_packs(qs, rest):
  match qs:
    case []:
      {==}
    case +q <> +t:
      tools_skip_packs.cons(q, t, rest, tools_skip_packs(t, rest))

# LAW: the lock `ez lock` renders names the hub it was resolved against
law lock_hub_read:
  for +ts: List<&2, M.Tool>
  for +hub: String
  for +ps: List<&2, L.Pack>
  {L.lock.hub(Laws.lock.doc(ts, hub, ps)) == hub : String}

def lock_hub_read(_ts, _hub, _ps):
  {==}

# LAW: and gives back its tool pins, as the lock gives them back
law lock_tools_read:
  for +ts: List<&2, M.Tool>
  for +hub: String
  for +ps: List<&2, L.Pack>
  {M.tools(Laws.lock.doc(ts, hub, ps)) == Laws.tools.canon(ts) : List<&2, M.Tool>}

def lock_tools_read(ts, _hub, ps):
  Equal.trans(List<&2, M.Tool>,
    M.tools(List.append(&2, T.Sect, L.pack.all(L.pack.sort(ps)), L.tool.sects(ts))),
    M.tools(L.tool.sects(ts)), Laws.tools.canon(ts),
    tools_skip_packs(L.pack.sort(ps), L.tool.sects(ts)), tools_read(ts))

# ---------------------------------------------------------------------------
# the packages a lock gives back

# whether no package's hash holds a quote. Proof vocabulary.
def hashes.clean(qs: List<&2, L.Pack>) -> Bool:
  match qs:
    case []:
      True{}
    case h <> t:
      Bool.and(Str.clear(L.pack.hash(h), '"'), hashes.clean(t))

# LAW: packages the planner lets through have no quote in any hash
law hashes_clean_ok:
  for +ps: List<&2, L.Pack>
  for +e: {P.packs.ok(ps) == True{} : Bool}
  {hashes.clean(ps) == True{} : Bool}

# one package, taken apart
law hashes_clean_ok.cons:
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for +e: {P.packs.ok(h <> t) == True{} : Bool}
  for ih: {hashes.clean(t) == True{} : Bool}
  {hashes.clean(h <> t) == True{} : Bool}

def hashes_clean_ok.cons(h, t, e, ih):
  match h:
    case L.Pack{+hash, +src, +fs}:
      and_true(Str.clear(hash, '"'), hashes.clean(t),
        clean_quote(hash, Eq.and.left(P.clean(hash),
          P.clean.all(List.append(&2, String, P.src.values(src), P.file.values(fs))),
          Eq.and.left(P.clean.all(P.pack.values(L.Pack{hash, src, fs})), Bool.not(L.has(t, hash)),
            Eq.and.right(P.paths.ok(fs), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src, fs})),
              Bool.not(L.has(t, hash))),
              Eq.and.left(Bool.and(P.paths.ok(fs), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src, fs})),
                Bool.not(L.has(t, hash)))), P.packs.ok(t), e))))),
        ih)

def hashes_clean_ok(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      hashes_clean_ok.cons(h, t, e, hashes_clean_ok(t, Eq.and.right(
        Bool.and(P.paths.ok(L.pack.files(h)), Bool.and(P.clean.all(P.pack.values(h)),
          Bool.not(L.has(t, L.pack.hash(h))))), P.packs.ok(t), e)))

# LAW: a package inserted among packages with clean hashes, when its hash is
# clean, one step, with how it compares given
law hclean_ins.step:
  for +p: L.Pack
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for b: Bool
  for +eq: {hashes.clean(h <> t) == True{} : Bool}
  for +ep: {Str.clear(L.pack.hash(p), '"') == True{} : Bool}
  for ih: {hashes.clean(L.pack.ins(t, p)) == True{} : Bool}
  {hashes.clean(L.pack.ins.put(b, p, h, t, L.pack.ins(t, p))) == True{} : Bool}

def hclean_ins.step(p, h, t, b, eq, ep, ih):
  match b:
    case True{}:
      and_true(Str.clear(L.pack.hash(p), '"'), hashes.clean(h <> t), ep, eq)
    case False{}:
      and_true(Str.clear(L.pack.hash(h), '"'), hashes.clean(L.pack.ins(t, p)),
        Eq.and.left(Str.clear(L.pack.hash(h), '"'), hashes.clean(t), eq), ih)

# LAW: and the whole insertion
law hclean_ins:
  for +qs: List<&2, L.Pack>
  for +p: L.Pack
  for +eq: {hashes.clean(qs) == True{} : Bool}
  for +ep: {Str.clear(L.pack.hash(p), '"') == True{} : Bool}
  {hashes.clean(L.pack.ins(qs, p)) == True{} : Bool}

def hclean_ins(qs, p, eq, ep):
  match qs:
    case []:
      and_true(Str.clear(L.pack.hash(p), '"'), True{}, ep, {==})
    case +h <> +t:
      hclean_ins.step(p, h, t, L.pack.le(p, h), eq, ep,
        hclean_ins(t, p, Eq.and.right(Str.clear(L.pack.hash(h), '"'), hashes.clean(t), eq), ep))

# LAW: packages with clean hashes, sorted, have clean hashes
law hclean_sort:
  for +ps: List<&2, L.Pack>
  for +e: {hashes.clean(ps) == True{} : Bool}
  {hashes.clean(L.pack.sort(ps)) == True{} : Bool}

def hclean_sort(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      hclean_ins(L.pack.sort(t), h,
        hclean_sort(t, Eq.and.right(Str.clear(L.pack.hash(h), '"'), hashes.clean(t), e)),
        Eq.and.left(Str.clear(L.pack.hash(h), '"'), hashes.clean(t), e))

# LAW: a hash fresh to packages and unequal to one more is fresh to them with
# it inserted, one step, with how it compares given
law fresh_ins.step:
  for +y: String
  for +x: L.Pack
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for b: Bool
  for +e1: {String.eq(y, L.pack.hash(x)) == False{} : Bool}
  for +e2: {Laws.hash.fresh(y, h <> t) == True{} : Bool}
  for ih: {Laws.hash.fresh(y, L.pack.ins(t, x)) == True{} : Bool}
  {Laws.hash.fresh(y, L.pack.ins.put(b, x, h, t, L.pack.ins(t, x))) == True{} : Bool}

def fresh_ins.step(y, x, h, t, b, e1, e2, ih):
  match b:
    case True{}:
      and_true(Bool.not(String.eq(y, L.pack.hash(x))), Laws.hash.fresh(y, h <> t),
        not_false(String.eq(y, L.pack.hash(x)), e1), e2)
    case False{}:
      and_true(Bool.not(String.eq(y, L.pack.hash(h))), Laws.hash.fresh(y, L.pack.ins(t, x)),
        Eq.and.left(Bool.not(String.eq(y, L.pack.hash(h))), Laws.hash.fresh(y, t), e2), ih)

# LAW: and the whole insertion
law fresh_ins:
  for +y: String
  for +qs: List<&2, L.Pack>
  for +x: L.Pack
  for +e1: {String.eq(y, L.pack.hash(x)) == False{} : Bool}
  for +e2: {Laws.hash.fresh(y, qs) == True{} : Bool}
  {Laws.hash.fresh(y, L.pack.ins(qs, x)) == True{} : Bool}

def fresh_ins(y, qs, x, e1, e2):
  match qs:
    case []:
      and_true(Bool.not(String.eq(y, L.pack.hash(x))), True{},
        not_false(String.eq(y, L.pack.hash(x)), e1), {==})
    case +h <> +t:
      fresh_ins.step(y, x, h, t, L.pack.le(x, h), e1, e2,
        fresh_ins(y, t, x, e1,
          Eq.and.right(Bool.not(String.eq(y, L.pack.hash(h))), Laws.hash.fresh(y, t), e2)))

# LAW: a hash fresh to packages is fresh to them sorted
law fresh_sort:
  for +y: String
  for +ps: List<&2, L.Pack>
  for +e: {Laws.hash.fresh(y, ps) == True{} : Bool}
  {Laws.hash.fresh(y, L.pack.sort(ps)) == True{} : Bool}

def fresh_sort(y, ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      fresh_ins(y, L.pack.sort(t), h,
        Eq.not.true(String.eq(y, L.pack.hash(h)),
          Eq.and.left(Bool.not(String.eq(y, L.pack.hash(h))), Laws.hash.fresh(y, t), e)),
        fresh_sort(y, t, Eq.and.right(Bool.not(String.eq(y, L.pack.hash(h))), Laws.hash.fresh(y, t), e)))

# LAW: a package inserted among distinct packages, when its hash is fresh to
# them, leaves them distinct, one step, with how it compares given
law distinct_ins.step:
  for +x: L.Pack
  for +h: L.Pack
  for +t: List<&2, L.Pack>
  for b: Bool
  for +ef: {Laws.hash.fresh(L.pack.hash(x), h <> t) == True{} : Bool}
  for +ed: {Laws.distinct(h <> t) == True{} : Bool}
  for ih: {Laws.distinct(L.pack.ins(t, x)) == True{} : Bool}
  {Laws.distinct(L.pack.ins.put(b, x, h, t, L.pack.ins(t, x))) == True{} : Bool}

def distinct_ins.step(x, h, t, b, ef, ed, ih):
  match b:
    case True{}:
      and_true(Laws.hash.fresh(L.pack.hash(x), h <> t), Laws.distinct(h <> t), ef, ed)
    case False{}:
      and_true(Laws.hash.fresh(L.pack.hash(h), L.pack.ins(t, x)), Laws.distinct(L.pack.ins(t, x)),
        fresh_ins(L.pack.hash(h), t, x,
          Str.eq_flip(L.pack.hash(x), L.pack.hash(h),
            Eq.not.true(String.eq(L.pack.hash(x), L.pack.hash(h)),
              Eq.and.left(Bool.not(String.eq(L.pack.hash(x), L.pack.hash(h))),
                Laws.hash.fresh(L.pack.hash(x), t), ef))),
          Eq.and.left(Laws.hash.fresh(L.pack.hash(h), t), Laws.distinct(t), ed)),
        ih)

# LAW: and the whole insertion
law distinct_ins:
  for +qs: List<&2, L.Pack>
  for +x: L.Pack
  for +ef: {Laws.hash.fresh(L.pack.hash(x), qs) == True{} : Bool}
  for +ed: {Laws.distinct(qs) == True{} : Bool}
  {Laws.distinct(L.pack.ins(qs, x)) == True{} : Bool}

def distinct_ins(qs, x, ef, ed):
  match qs:
    case []:
      {==}
    case +h <> +t:
      distinct_ins.step(x, h, t, L.pack.le(x, h), ef, ed,
        distinct_ins(t, x,
          Eq.and.right(Bool.not(String.eq(L.pack.hash(x), L.pack.hash(h))),
            Laws.hash.fresh(L.pack.hash(x), t), ef),
          Eq.and.right(Laws.hash.fresh(L.pack.hash(h), t), Laws.distinct(t), ed)))

# LAW: distinct packages, sorted, are distinct
law distinct_sort:
  for +ps: List<&2, L.Pack>
  for +e: {Laws.distinct(ps) == True{} : Bool}
  {Laws.distinct(L.pack.sort(ps)) == True{} : Bool}

def distinct_sort(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      distinct_ins(L.pack.sort(t), h,
        fresh_sort(L.pack.hash(h), t,
          Eq.and.left(Laws.hash.fresh(L.pack.hash(h), t), Laws.distinct(t), e)),
        distinct_sort(t, Eq.and.right(Laws.hash.fresh(L.pack.hash(h), t), Laws.distinct(t), e)))

# LAW: packages the planner lets through are distinct
law packs_distinct:
  for +ps: List<&2, L.Pack>
  for +e: {P.packs.ok(ps) == True{} : Bool}
  {Laws.distinct(ps) == True{} : Bool}

def packs_distinct(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      +ok = Eq.and.left(Bool.and(P.paths.ok(L.pack.files(h)), Bool.and(P.clean.all(P.pack.values(h)),
          Bool.not(L.has(t, L.pack.hash(h))))), P.packs.ok(t), e)
      and_true(Laws.hash.fresh(L.pack.hash(h), t), Laws.distinct(t),
        has_fresh(t, L.pack.hash(h), Eq.not.true(L.has(t, L.pack.hash(h)),
          Eq.and.right(P.clean.all(P.pack.values(h)), Bool.not(L.has(t, L.pack.hash(h))),
            Eq.and.right(P.paths.ok(L.pack.files(h)), Bool.and(P.clean.all(P.pack.values(h)),
              Bool.not(L.has(t, L.pack.hash(h)))), ok)))),
        packs_distinct(t, Eq.and.right(Bool.and(P.paths.ok(L.pack.files(h)),
          Bool.and(P.clean.all(P.pack.values(h)), Bool.not(L.has(t, L.pack.hash(h))))),
          P.packs.ok(t), e)))

# every package's hash, in the order given. Proof vocabulary.
def hash.all(qs: List<&2, L.Pack>) -> List<&2, String>:
  match qs:
    case []:
      []
    case h <> t:
      L.pack.hash(h) <> hash.all(t)

# LAW: a package's source table names no hash of its own
law hput_source:
  for +h: String
  for +s: L.Src
  for +rest: List<&2, String>
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  {L.hash.put(L.named3(L.segs(T.Sect{pack.name(h, "source"), L.src.pairs(s)}), "packages", "files"),
    T.Sect{pack.name(h, "source"), L.src.pairs(s)}, rest) == rest : List<&2, String>}

def hput_source(h, s, rest, eh):
  g = Equal.sym(List<&2, String>, T.segments(pack.name(h, "source")), ["packages", h, "source"],
    seg_pack(h, "source", eh, {==}, {==}))
  %g : {L.hash.put(L.named3(_, "packages", "files"),
    T.Sect{pack.name(h, "source"), L.src.pairs(s)}, rest) == rest : List<&2, String>}
  {==}

# LAW: and its files table names its hash
law hput_files:
  for +h: String
  for +fs: List<&2, K.File>
  for +rest: List<&2, String>
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  {L.hash.put(L.named3(L.segs(T.Sect{pack.name(h, "files"), L.file.pairs(fs)}), "packages", "files"),
    T.Sect{pack.name(h, "files"), L.file.pairs(fs)}, rest) == h <> rest : List<&2, String>}

def hput_files(h, fs, rest, eh):
  g = Equal.sym(List<&2, String>, T.segments(pack.name(h, "files")), ["packages", h, "files"],
    seg_pack(h, "files", eh, {==}, {==}))
  %g : {L.hash.put(L.named3(_, "packages", "files"),
    T.Sect{pack.name(h, "files"), L.file.pairs(fs)}, rest) == h <> rest : List<&2, String>}
  g2 = Equal.sym(List<&2, String>, T.segments(pack.name(h, "files")), ["packages", h, "files"],
    seg_pack(h, "files", eh, {==}, {==}))
  %g2 : {K.word(_, 1n) <> rest == h <> rest : List<&2, String>}
  {==}

# LAW: the hashes the packages' tables name, then whatever follows names
law hashes_packs:
  for +qs: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +e: {hashes.clean(qs) == True{} : Bool}
  {L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys))
    == List.append(&2, String, hash.all(qs), L.hashes(ys)) : List<&2, String>}

# one package, taken apart
law hashes_packs.cons:
  for +q: L.Pack
  for +qs: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +eh: {Str.clear(L.pack.hash(q), '"') == True{} : Bool}
  for ih: {L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys))
    == List.append(&2, String, hash.all(qs), L.hashes(ys)) : List<&2, String>}
  {L.hashes(List.append(&2, T.Sect, L.pack.all(q <> qs), ys))
    == List.append(&2, String, hash.all(q <> qs), L.hashes(ys)) : List<&2, String>}

def hashes_packs.cons(q, qs, ys, eh, ih):
  match q:
    case L.Pack{+h, +s, +f}:
      Equal.trans(List<&2, String>,
        L.hashes(List.append(&2, T.Sect, L.pack.all(L.Pack{h, s, f} <> qs), ys)),
        L.hash.put(L.named3(L.segs(T.Sect{pack.name(h, "files"), L.file.pairs(K.files_of(f))}),
          "packages", "files"), T.Sect{pack.name(h, "files"), L.file.pairs(K.files_of(f))},
          L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys))),
        List.append(&2, String, hash.all(L.Pack{h, s, f} <> qs), L.hashes(ys)),
        hput_source(h, s, L.hash.put(L.named3(L.segs(T.Sect{pack.name(h, "files"),
          L.file.pairs(K.files_of(f))}), "packages", "files"),
          T.Sect{pack.name(h, "files"), L.file.pairs(K.files_of(f))},
          L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys))), eh),
        Equal.trans(List<&2, String>,
          L.hash.put(L.named3(L.segs(T.Sect{pack.name(h, "files"), L.file.pairs(K.files_of(f))}),
            "packages", "files"), T.Sect{pack.name(h, "files"), L.file.pairs(K.files_of(f))},
            L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys))),
          h <> L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys)),
          List.append(&2, String, hash.all(L.Pack{h, s, f} <> qs), L.hashes(ys)),
          hput_files(h, K.files_of(f), L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys)), eh),
          Equal.cong(List<&2, String>, List<&2, String>, r => h <> r,
            L.hashes(List.append(&2, T.Sect, L.pack.all(qs), ys)),
            List.append(&2, String, hash.all(qs), L.hashes(ys)), ih)))

def hashes_packs(qs, ys, e):
  match qs:
    case []:
      {==}
    case +q <> +t:
      hashes_packs.cons(q, t, ys,
        Eq.and.left(Str.clear(L.pack.hash(q), '"'), hashes.clean(t), e),
        hashes_packs(t, ys, Eq.and.right(Str.clear(L.pack.hash(q), '"'), hashes.clean(t), e)))

# LAW: a tool's table names no hash
law hashes_tools:
  for +ts: List<&2, M.Tool>
  {L.hashes(L.tool.sects(ts)) == [] : List<&2, String>}

# one tool, taken apart
law hashes_tools.cons:
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for ih: {L.hashes(L.tool.sects(t)) == [] : List<&2, String>}
  {L.hashes(L.tool.sects(h <> t)) == [] : List<&2, String>}

def hashes_tools.cons(h, t, ih):
  match h:
    case M.Tool{+n, +e, +b, +s}:
      w = Equal.sym(String, K.word(T.segments("tools." ++ n), 0n), "tools", seg_tools(n))
      %w : {L.hash.put(Bool.and(Nat.is_eq(List.length(&2, String, T.segments("tools." ++ n)), 3n),
        Bool.and(String.eq(_, "packages"), String.eq(K.word(T.segments("tools." ++ n), 2n), "files"))),
        L.tool.sect(M.Tool{n, e, b, s}), L.hashes(L.tool.sects(t))) == [] : List<&2, String>}
      a = Equal.sym(Bool, Bool.and(Nat.is_eq(List.length(&2, String, T.segments("tools." ++ n)), 3n),
        False{}), False{}, and_false(Nat.is_eq(List.length(&2, String, T.segments("tools." ++ n)), 3n)))
      %a : {L.hash.put(_, L.tool.sect(M.Tool{n, e, b, s}), L.hashes(L.tool.sects(t))) == []
        : List<&2, String>}
      ih

def hashes_tools(ts):
  match ts:
    case []:
      {==}
    case +h <> +t:
      hashes_tools.cons(h, t, hashes_tools(t))

# a package's two tables, spelled as the proofs spell them. Proof vocabulary.
def pk.src(h: String, s: L.Src) -> T.Sect:
  T.Sect{pack.name(h, "source"), L.src.pairs(s)}

def pk.files(h: String, f: List<&2, K.File>) -> T.Sect:
  T.Sect{pack.name(h, "files"), L.file.pairs(K.files_of(f))}

# LAW: a lookup for another hash passes over a package's two tables
law at_skip:
  for +h: String
  for +s: L.Src
  for +f: List<&2, K.File>
  for +r: List<&2, T.Sect>
  for +k: String
  for +x: String
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  for +e: {String.eq(h, k) == False{} : Bool}
  {L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), r), "packages", k, x)
    == L.at3(r, "packages", k, x) : List<&2, T.Kv>}

def at_skip(h, s, f, r, k, x, eh, e):
  g1 = Equal.sym(List<&2, String>, T.segments(pack.name(h, "source")), ["packages", h, "source"],
    seg_pack(h, "source", eh, {==}, {==}))
  %g1 : {L.at.pick(L.is3(_, "packages", k, x), pk.src(h, s),
    L.at.pick(L.is3(L.segs(pk.files(h, f)), "packages", k, x), pk.files(h, f), L.at3(r, "packages", k, x)))
    == L.at3(r, "packages", k, x) : List<&2, T.Kv>}
  g2 = Equal.sym(List<&2, String>, T.segments(pack.name(h, "files")), ["packages", h, "files"],
    seg_pack(h, "files", eh, {==}, {==}))
  %g2 : {L.at.pick(L.is3(["packages", h, "source"], "packages", k, x), pk.src(h, s),
    L.at.pick(L.is3(_, "packages", k, x), pk.files(h, f), L.at3(r, "packages", k, x)))
    == L.at3(r, "packages", k, x) : List<&2, T.Kv>}
  f1 = Equal.sym(Bool, String.eq(h, k), False{}, e)
  %f1 : {L.at.pick(Bool.and(_, String.eq("source", x)), pk.src(h, s),
    L.at.pick(Bool.and(_, String.eq("files", x)), pk.files(h, f), L.at3(r, "packages", k, x)))
    == L.at3(r, "packages", k, x) : List<&2, T.Kv>}
  {==}

# LAW: a lookup for a package's own source finds its source table
law at_hit_src:
  for +h: String
  for +s: L.Src
  for +f: List<&2, K.File>
  for +r: List<&2, T.Sect>
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  {L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), r), "packages", h, "source")
    == L.src.pairs(s) : List<&2, T.Kv>}

def at_hit_src(h, s, f, r, eh):
  g1 = Equal.sym(List<&2, String>, T.segments(pack.name(h, "source")), ["packages", h, "source"],
    seg_pack(h, "source", eh, {==}, {==}))
  %g1 : {L.at.pick(L.is3(_, "packages", h, "source"), pk.src(h, s),
    L.at.pick(L.is3(L.segs(pk.files(h, f)), "packages", h, "source"), pk.files(h, f),
      L.at3(r, "packages", h, "source"))) == L.src.pairs(s) : List<&2, T.Kv>}
  q = Equal.sym(Bool, String.eq(h, h), True{}, Eq.string_eq_self(h))
  %q : {L.at.pick(Bool.and(_, True{}), pk.src(h, s),
    L.at.pick(L.is3(L.segs(pk.files(h, f)), "packages", h, "source"), pk.files(h, f),
      L.at3(r, "packages", h, "source"))) == L.src.pairs(s) : List<&2, T.Kv>}
  {==}

# LAW: and a lookup for its files finds its files table
law at_hit_files:
  for +h: String
  for +s: L.Src
  for +f: List<&2, K.File>
  for +r: List<&2, T.Sect>
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  {L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), r), "packages", h, "files")
    == L.file.pairs(K.files_of(f)) : List<&2, T.Kv>}

def at_hit_files(h, s, f, r, eh):
  g1 = Equal.sym(List<&2, String>, T.segments(pack.name(h, "source")), ["packages", h, "source"],
    seg_pack(h, "source", eh, {==}, {==}))
  %g1 : {L.at.pick(L.is3(_, "packages", h, "files"), pk.src(h, s),
    L.at.pick(L.is3(L.segs(pk.files(h, f)), "packages", h, "files"), pk.files(h, f),
      L.at3(r, "packages", h, "files"))) == L.file.pairs(K.files_of(f)) : List<&2, T.Kv>}
  g2 = Equal.sym(List<&2, String>, T.segments(pack.name(h, "files")), ["packages", h, "files"],
    seg_pack(h, "files", eh, {==}, {==}))
  %g2 : {L.at.pick(L.is3(["packages", h, "source"], "packages", h, "files"), pk.src(h, s),
    L.at.pick(L.is3(_, "packages", h, "files"), pk.files(h, f),
      L.at3(r, "packages", h, "files"))) == L.file.pairs(K.files_of(f)) : List<&2, T.Kv>}
  q = Equal.sym(Bool, String.eq(h, h), True{}, Eq.string_eq_self(h))
  %q : {L.at.pick(Bool.and(_, False{}), pk.src(h, s),
    L.at.pick(Bool.and(_, True{}), pk.files(h, f),
      L.at3(r, "packages", h, "files"))) == L.file.pairs(K.files_of(f)) : List<&2, T.Kv>}
  {==}

# the document from its packages' tables on. Proof vocabulary.
def doc.at(hub: String, qs: List<&2, L.Pack>, ys: List<&2, T.Sect>) -> List<&2, T.Sect>:
  L.lock.sect(hub) <> List.append(&2, T.Sect, L.pack.all(qs), ys)

# LAW: the package a lock records under a hash, when it is the first
# package, is that package as the lock gives it back
law pack_of_hit:
  for +hub: String
  for +h: String
  for +s: L.Src
  for +f: List<&2, K.File>
  for +qs: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  {L.pack_of(doc.at(hub, L.Pack{h, s, f} <> qs, ys), h) == L.Pack{h, s, K.files_of(f)} : L.Pack}

def pack_of_hit(_hub, h, s, f, qs, ys, eh):
  a1 = Equal.sym(List<&2, T.Kv>,
    L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), List.append(&2, T.Sect, L.pack.all(qs), ys)),
      "packages", h, "source"),
    L.src.pairs(s), at_hit_src(h, s, f, List.append(&2, T.Sect, L.pack.all(qs), ys), eh))
  %a1 : {L.Pack{h, L.src_of(_), L.pair.files(L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}),
    List.append(&2, T.Sect, L.pack.all(qs), ys)), "packages", h, "files"))}
    == L.Pack{h, s, K.files_of(f)} : L.Pack}
  a2 = Equal.sym(List<&2, T.Kv>,
    L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), List.append(&2, T.Sect, L.pack.all(qs), ys)),
      "packages", h, "files"),
    L.file.pairs(K.files_of(f)), at_hit_files(h, s, f, List.append(&2, T.Sect, L.pack.all(qs), ys), eh))
  %a2 : {L.Pack{h, L.src_of(L.src.pairs(s)), L.pair.files(_)} == L.Pack{h, s, K.files_of(f)} : L.Pack}
  a3 = Equal.sym(L.Src, L.src_of(L.src.pairs(s)), s, src_read(s))
  %a3 : {L.Pack{h, _, L.pair.files(L.file.pairs(K.files_of(f)))} == L.Pack{h, s, K.files_of(f)} : L.Pack}
  a4 = Equal.sym(List<&2, K.File>, L.pair.files(L.file.pairs(K.files_of(f))), K.files_of(f),
    pair_files(K.files_of(f)))
  %a4 : {L.Pack{h, s, _} == L.Pack{h, s, K.files_of(f)} : L.Pack}
  {==}

# LAW: a lookup for another hash passes over the first package
law pack_of_skip:
  for +hub: String
  for +h: String
  for +s: L.Src
  for +f: List<&2, K.File>
  for +qs: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +k: String
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  for +e: {String.eq(h, k) == False{} : Bool}
  {L.pack_of(doc.at(hub, L.Pack{h, s, f} <> qs, ys), k) == L.pack_of(doc.at(hub, qs, ys), k) : L.Pack}

def pack_of_skip(hub, h, s, f, qs, ys, k, eh, e):
  a1 = Equal.sym(List<&2, T.Kv>,
    L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), List.append(&2, T.Sect, L.pack.all(qs), ys)),
      "packages", k, "source"),
    L.at3(List.append(&2, T.Sect, L.pack.all(qs), ys), "packages", k, "source"),
    at_skip(h, s, f, List.append(&2, T.Sect, L.pack.all(qs), ys), k, "source", eh, e))
  %a1 : {L.Pack{k, L.src_of(_), L.pair.files(L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}),
    List.append(&2, T.Sect, L.pack.all(qs), ys)), "packages", k, "files"))}
    == L.pack_of(doc.at(hub, qs, ys), k) : L.Pack}
  a2 = Equal.sym(List<&2, T.Kv>,
    L.at3(List.append(&2, T.Sect, L.pack.sects(L.Pack{h, s, f}), List.append(&2, T.Sect, L.pack.all(qs), ys)),
      "packages", k, "files"),
    L.at3(List.append(&2, T.Sect, L.pack.all(qs), ys), "packages", k, "files"),
    at_skip(h, s, f, List.append(&2, T.Sect, L.pack.all(qs), ys), k, "files", eh, e))
  %a2 : {L.Pack{k, L.src_of(L.at3(List.append(&2, T.Sect, L.pack.all(qs), ys), "packages", k, "source")),
    L.pair.files(_)} == L.pack_of(doc.at(hub, qs, ys), k) : L.Pack}
  {==}

# LAW: the packages a lock records under hashes the first package's is fresh
# to are the ones recorded without it
law packs_at_skip:
  for +hub: String
  for +h: String
  for +s: L.Src
  for +f: List<&2, K.File>
  for +qs: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +rs: List<&2, L.Pack>
  for +eh: {Str.clear(h, '"') == True{} : Bool}
  for +ef: {Laws.hash.fresh(h, rs) == True{} : Bool}
  {L.packs.at(doc.at(hub, L.Pack{h, s, f} <> qs, ys), hash.all(rs))
    == L.packs.at(doc.at(hub, qs, ys), hash.all(rs)) : List<&2, L.Pack>}

def packs_at_skip(hub, h, s, f, qs, ys, rs, eh, ef):
  match rs:
    case []:
      {==}
    case +r <> +rt:
      p1 = Equal.sym(L.Pack, L.pack_of(doc.at(hub, L.Pack{h, s, f} <> qs, ys), L.pack.hash(r)),
        L.pack_of(doc.at(hub, qs, ys), L.pack.hash(r)),
        pack_of_skip(hub, h, s, f, qs, ys, L.pack.hash(r), eh,
          Eq.not.true(String.eq(h, L.pack.hash(r)),
            Eq.and.left(Bool.not(String.eq(h, L.pack.hash(r))), Laws.hash.fresh(h, rt), ef))))
      %p1 : {_ <> L.packs.at(doc.at(hub, L.Pack{h, s, f} <> qs, ys), hash.all(rt))
        == L.pack_of(doc.at(hub, qs, ys), L.pack.hash(r)) <> L.packs.at(doc.at(hub, qs, ys), hash.all(rt))
        : List<&2, L.Pack>}
      Equal.cong(List<&2, L.Pack>, List<&2, L.Pack>,
        x => L.pack_of(doc.at(hub, qs, ys), L.pack.hash(r)) <> x,
        L.packs.at(doc.at(hub, L.Pack{h, s, f} <> qs, ys), hash.all(rt)),
        L.packs.at(doc.at(hub, qs, ys), hash.all(rt)),
        packs_at_skip(hub, h, s, f, qs, ys, rt, eh,
          Eq.and.right(Bool.not(String.eq(h, L.pack.hash(r))), Laws.hash.fresh(h, rt), ef)))

# LAW: the packages a lock records under its packages' hashes are its
# packages as it gives them back, one package, taken apart
law packs_at_all.cons:
  for +hub: String
  for +q: L.Pack
  for +t: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +eh: {Str.clear(L.pack.hash(q), '"') == True{} : Bool}
  for +ef: {Laws.hash.fresh(L.pack.hash(q), t) == True{} : Bool}
  for ih: {L.packs.at(doc.at(hub, t, ys), hash.all(t)) == Laws.canon.all(t) : List<&2, L.Pack>}
  {L.packs.at(doc.at(hub, q <> t, ys), hash.all(q <> t)) == Laws.canon.all(q <> t) : List<&2, L.Pack>}

def packs_at_all.cons(hub, q, t, ys, eh, ef, ih):
  match q:
    case L.Pack{+h, +s, +f}:
      p1 = Equal.sym(L.Pack, L.pack_of(doc.at(hub, L.Pack{h, s, f} <> t, ys), h),
        L.Pack{h, s, K.files_of(f)}, pack_of_hit(hub, h, s, f, t, ys, eh))
      %p1 : {_ <> L.packs.at(doc.at(hub, L.Pack{h, s, f} <> t, ys), hash.all(t))
        == Laws.canon.all(L.Pack{h, s, f} <> t) : List<&2, L.Pack>}
      p2 = Equal.sym(List<&2, L.Pack>, L.packs.at(doc.at(hub, L.Pack{h, s, f} <> t, ys), hash.all(t)),
        L.packs.at(doc.at(hub, t, ys), hash.all(t)),
        packs_at_skip(hub, h, s, f, t, ys, t, eh, ef))
      %p2 : {L.Pack{h, s, K.files_of(f)} <> _ == Laws.canon.all(L.Pack{h, s, f} <> t) : List<&2, L.Pack>}
      Equal.cong(List<&2, L.Pack>, List<&2, L.Pack>, x => L.Pack{h, s, K.files_of(f)} <> x,
        L.packs.at(doc.at(hub, t, ys), hash.all(t)), Laws.canon.all(t), ih)

# LAW: the packages a lock records under its packages' hashes are its
# packages as it gives them back, when the hashes are distinct and hold no
# quote
law packs_at_all:
  for +hub: String
  for +qs: List<&2, L.Pack>
  for +ys: List<&2, T.Sect>
  for +ed: {Laws.distinct(qs) == True{} : Bool}
  for +ec: {hashes.clean(qs) == True{} : Bool}
  {L.packs.at(doc.at(hub, qs, ys), hash.all(qs)) == Laws.canon.all(qs) : List<&2, L.Pack>}

def packs_at_all(hub, qs, ys, ed, ec):
  match qs:
    case []:
      {==}
    case +q <> +t:
      packs_at_all.cons(hub, q, t, ys,
        Eq.and.left(Str.clear(L.pack.hash(q), '"'), hashes.clean(t), ec),
        Eq.and.left(Laws.hash.fresh(L.pack.hash(q), t), Laws.distinct(t), ed),
        packs_at_all(hub, t, ys,
          Eq.and.right(Laws.hash.fresh(L.pack.hash(q), t), Laws.distinct(t), ed),
          Eq.and.right(Str.clear(L.pack.hash(q), '"'), hashes.clean(t), ec)))

# LAW: the hashes a lock's document names are its packages', in hash order
law hashes_doc:
  for +ts: List<&2, M.Tool>
  for +hub: String
  for +ps: List<&2, L.Pack>
  for +e: {hashes.clean(L.pack.sort(ps)) == True{} : Bool}
  {L.hashes(Laws.lock.doc(ts, hub, ps)) == hash.all(L.pack.sort(ps)) : List<&2, String>}

def hashes_doc(ts, _hub, ps, e):
  h1 = Equal.sym(List<&2, String>,
    L.hashes(List.append(&2, T.Sect, L.pack.all(L.pack.sort(ps)), L.tool.sects(ts))),
    List.append(&2, String, hash.all(L.pack.sort(ps)), L.hashes(L.tool.sects(ts))),
    hashes_packs(L.pack.sort(ps), L.tool.sects(ts), e))
  %h1 : {_ == hash.all(L.pack.sort(ps)) : List<&2, String>}
  h2 = Equal.sym(List<&2, String>, L.hashes(L.tool.sects(ts)), [], hashes_tools(ts))
  %h2 : {List.append(&2, String, hash.all(L.pack.sort(ps)), _) == hash.all(L.pack.sort(ps))
    : List<&2, String>}
  Str.list_append_nil(String, hash.all(L.pack.sort(ps)))

# LAW: the packages a lockable lock's document gives back are its packages
# as the lock gives them back
law lock_packs_read:
  for +ts: List<&2, M.Tool>
  for +hub: String
  for +ps: List<&2, L.Pack>
  for +ok: {P.lockable(ps, ts, hub) == True{} : Bool}
  {L.packs(Laws.lock.doc(ts, hub, ps)) == Laws.canon(ps) : List<&2, L.Pack>}

def lock_packs_read(ts, hub, ps, ok):
  +pk = Eq.and.left(P.packs.ok(ps), P.tools.ok(ts),
    Eq.and.right(P.clean(hub), Bool.and(P.packs.ok(ps), P.tools.ok(ts)), ok))
  +hc = hclean_sort(ps, hashes_clean_ok(ps, pk))
  h = Equal.sym(List<&2, String>, L.hashes(Laws.lock.doc(ts, hub, ps)), hash.all(L.pack.sort(ps)),
    hashes_doc(ts, hub, ps, hc))
  %h : {L.packs.at(Laws.lock.doc(ts, hub, ps), _) == Laws.canon(ps) : List<&2, L.Pack>}
  packs_at_all(hub, L.pack.sort(ps), L.tool.sects(ts), distinct_sort(ps, packs_distinct(ps, pk)), hc)

def Laws.lock_reads_back(ps, ts, hub, ok):
  s = Equal.sym(List<&2, T.Sect>, T.sects(T.parse(L.render.tools(ts, hub, ps))),
    Laws.lock.doc(ts, hub, ps), Laws.lock_sections_read_back(ps, ts, hub, ok))
  %s : {L.packs(_) == Laws.canon(ps) : List<&2, L.Pack>}
  lock_packs_read(ts, hub, ps, ok)

def Laws.lock_hub_reads_back(ps, ts, hub, ok):
  s = Equal.sym(List<&2, T.Sect>, T.sects(T.parse(L.render.tools(ts, hub, ps))),
    Laws.lock.doc(ts, hub, ps), Laws.lock_sections_read_back(ps, ts, hub, ok))
  %s : {L.lock.hub(_) == hub : String}
  lock_hub_read(ts, hub, ps)

def Laws.lock_tools_read_back(ps, ts, hub, ok):
  s = Equal.sym(List<&2, T.Sect>, T.sects(T.parse(L.render.tools(ts, hub, ps))),
    Laws.lock.doc(ts, hub, ps), Laws.lock_sections_read_back(ps, ts, hub, ok))
  %s : {M.tools(_) == Laws.tools.canon(ts) : List<&2, M.Tool>}
  lock_tools_read(ts, hub, ps)
