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
import ../check/toml.bend as Toml
import ../pkg/pkg.bend as K
import ../pkg/LAWS.bend as KL
import ../pkg/PROOF.bend as KP
import ../manifest/ignore.bend as I
import ../manifest/render.bend as Rend
import ../manifest/LAWS.bend as ML
import ../manifest/PROOF.bend as MP
import ../git/git.bend as Git
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

# A plain World's args say no `--upgrade`, and it leaves what a plain lock
# leaves; the other arm contradicts the premise.
def Laws.lock_idempotent(w, e):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.put(Laws.after(W.World{W.Args{True{}, only}, ledger, listing,
                replies, ups}), "ez.lock.toml") == P.put(W.World{W.Args{True{}, only}, ledger,
                listing, replies, ups}, "ez.lock.toml") : P.Wrote}, e)
            case False{}:
              after.pick_put(P.refuses(W.World{W.Args{False{}, only}, ledger, listing, replies, ups}),
                W.World{W.Args{False{}, only}, ledger, listing, replies, ups})

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

# LAW: a plain lock that succeeded leaves no tree for the next to lay
law relock.plain:
  for +w: W.World
  for ok: {P.refuses(w) == False{} : Bool}
  {Laws.fresh(Laws.after.pick(P.refuses(w), w)) == [] : List<&2, String>}

def relock.plain(w, ok):
  Equal.trans(List<&2, String>,
    Laws.fresh(Laws.after.pick(P.refuses(w), w)),
    Laws.fresh(Laws.after.pick(False{}, w)),
    [],
    Equal.cong(Bool, List<&2, String>, b => Laws.fresh(Laws.after.pick(b, w)),
      P.refuses(w), False{}, ok),
    fresh.laid(w))

def Laws.relock_lays_nothing(w, e, ok):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {Laws.fresh(Laws.after(W.World{W.Args{True{}, only}, ledger, listing,
                replies, ups})) == [] : List<&2, String>}, e)
            case False{}:
              relock.plain(W.World{W.Args{False{}, only}, ledger, listing, replies, ups}, ok)

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

law tpin_name:
  for short: Bool
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  {pinned.name(Up.tool.pin(short, tool, rev, tag, nar, says), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tpin_name(short, tool, rev, tag, nar, _says):
  match short:
    case True{}:
      {==}
    case False{}:
      set_name(tool, rev, tag, nar)

law weighed_name:
  for wd: Up.Wd
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {pinned.name(Up.tool.weighed(wd, tool, rev, tag, says), M.tool.name(tool))
    == M.tool.name(tool) : String}

def weighed_name(wd, tool, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      tpin_name(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +ref: String
  {pinned.name(Up.tool.resolved(tip, rs, tool, ref), M.tool.name(tool)) == M.tool.name(tool) : String}

def resolved_name(tip, rs, tool, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
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
    case Up.Named{+ref}:
      resolved_name(Up.follow(rs, url, ref), rs, tool, ref)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

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
    case U.Advance{+rev, _tag}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, "",
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_nar_name:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +nar: String
  {pinned.name(Up.tool.kept.nar(fill, rs, tool, tip, tag, nar), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tkept_nar_name(fill, rs, tool, tip, tag, nar):
  match fill:
    case True{}:
      tpin_name(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tverdict_name(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")

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
      tkept_nar_name(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
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
      taim_name(U.aim(True{}, M.tool.source(tool)), rs, tool)

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

# What an upgrade writes around the ledger (EZ-VEN-1, EZ-VEN-2, EZ-VEN-3). The
# upgrade's own files are ez.toml and `.gitignore`, and nothing else: each
# stage of `Up.next` either stops with no file or goes on, and the last one,
# `Up.done`, writes ez.toml over the ledger it leaves when a pin moved and
# `.gitignore` as `I.sync` makes it from the file it read. `ok.next` says
# that of a decision; every decision `Up.next` makes is one. The sources are
# written after them, one write per source whose text the moves change, and
# the lock last.

# what one of the upgrade's own files may be: ez.toml over the ledger the
# model renders, or `.gitignore` with the allowlist of the hashes it commits
# and the lines of the file it read that are not ez's. Law vocabulary: ez
# never calls it.
def ok.go(
  toml: Bool,
  gi: Bool,
  +t: String,
  +vs: List<&2, String>,
  model: M.Read,
  +ig: String
) -> Type:
  match toml gi:
    case True{} _:
      {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}
    case False{} True{}:
      {Str.clear.all(vs, '\n') == True{} : Bool} ->
        ({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
          {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>})
    case False{} False{}:
      Empty

# one file the upgrade writes, so
def ok.edit(e: Up.Edit, +vs: List<&2, String>, +model: M.Read, +ig: String) -> Type:
  Up.Edit{+p, t} = e
  ok.go(String.eq(p, "ez.toml"), String.eq(p, ".gitignore"), t, vs, model, ig)

# every file the upgrade writes, so
def ok.edits(es: List<&2, Up.Edit>, +vs: List<&2, String>, +model: M.Read, +ig: String) -> Type:
  match es:
    case []:
      Unit
    case e <> t:
      ok.edit(e, vs, model, ig) & ok.edits(t, vs, model, ig)

# what the upgrade decided, over `.gitignore` as it read it
def ok.next(+nx: Up.Next, +ig: String) -> Type:
  ok.edits(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig)

# LAW: the files `Up.done` writes, with whether a pin moved and whether the
# allowlist changed the file given as parameters
law ok_done.arm:
  for moved: Bool
  for b: Bool
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +ig: String
  ok.edits(Up.edit.toml(moved, Rend.show(M.Manifest{pn, pe, pb, hb, ds, ts}),
      Up.edit.if(b, ".gitignore", I.sync(ds, ig), [])),
    I.vended(ds),
    Up.model.next(moved, M.Manifest{pn, pe, pb, hb, ds, ts}, M.Manifest{pn, pe, pb, hb, ods, ots}),
    ig)

def ok_done.arm(moved, b, _pn, _pe, _pb, _hb, ds, _ts, _ods, _ots, ig):
  match moved b:
    case True{} True{}:
      ({==}, Unit{})
    case True{} False{}:
      ({==}, (+ev => (ML.sync_allowlist_is_the_ledger(ds, ig, ev),
        ML.sync_keeps_other_lines(ds, ig, ev)), Unit{}))
    case False{} True{}:
      Unit{}
    case False{} False{}:
      (+ev => (ML.sync_allowlist_is_the_ledger(ds, ig, ev),
        ML.sync_keeps_other_lines(ds, ig, ev)), Unit{})

law ok_done:
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ig: String
  for fs: List<&2, Up.Found>
  ok.next(Up.done(M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt, ig, fs), ig)

def ok_done(pn, pe, pb, hb, ods, ots, dd, tt, ig, _fs):
  match dd:
    case Up.Deps{+ds, ss, es, dm, dsy, dtr, das, dbad}:
      match tt:
        case Up.Tools{+ts, tm, tsy, tas, tbad}:
          ok_done.arm(Bool.or(dm, tm), String.eq(I.sync(ds, ig), ig), pn, pe, pb, hb,
            ds, ts, ods, ots, ig)

law ok_srcs:
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ig: String
  ok.next(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt, ig), ig)

def ok_srcs(srcs, pn, pe, pb, hb, ods, ots, dd, tt, ig):
  match srcs:
    case Up.Srcs{fs}:
      ok_done(pn, pe, pb, hb, ods, ots, dd, tt, ig, fs)
    case Up.SrcsWait{_ask}:
      Unit{}
    case Up.SrcsNo{_why}:
      Unit{}

law ok_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for +tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for es: {Up.text.said(rs, Up.Ignore{}) == said : Up.Said}
  ok.next(Up.got.ignore(said, srcs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt),
    Laws.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_ignore(said, srcs, pn, pe, pb, hb, ods, ots, dd, tt, rs, es):
  match said:
    case Up.Said{+x}:
      %Equal.sym(Up.Said, Up.text.said(rs, Up.Ignore{}), Up.Said{x}, es)
        : ok.next(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt, x),
          Laws.ignore.said(_))
      ok_srcs(srcs, pn, pe, pb, hb, ods, ots, dd, tt, x)
    case Up.Unsaid{_why}:
      Unit{}
    case Up.Unasked{_ask}:
      Unit{}

law ok_asks:
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for +tt: Up.Tools
  ok.next(Up.pins.asks(asks, rs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt),
    Laws.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_asks(asks, rs, pn, pe, pb, hb, ods, ots, dd, tt):
  match asks:
    case []:
      ok_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd)), rs),
        pn, pe, pb, hb, ods, ots, dd, tt, rs, {==})
    case _h <> _t:
      Unit{}

law ok_bad:
  for clean: Bool
  for +bad: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for +tt: Up.Tools
  ok.next(Up.pins.bad(clean, bad, asks, rs, M.Manifest{pn, pe, pb, hb, ods, ots}, dd, tt),
    Laws.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_bad(clean, _bad, asks, rs, pn, pe, pb, hb, ods, ots, dd, tt):
  match clean:
    case True{}:
      ok_asks(asks, rs, pn, pe, pb, hb, ods, ots, dd, tt)
    case False{}:
      Unit{}

law ok_pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  ok.next(Up.pins(dd, tt, rs, M.Manifest{pn, pe, pb, hb, ods, ots}),
    Laws.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_pins(dd, tt, rs, pn, pe, pb, hb, ods, ots):
  match dd:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad}:
      match tt:
        case Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
          ok_bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            List.append(&2, Up.Ask, das, tas), rs, pn, pe, pb, hb, ods, ots,
            Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""})

law ok_known:
  for ok: Bool
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  ok.next(Up.known(ok, only, rs, M.Manifest{pn, pe, pb, hb, ods, ots}),
    Laws.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_known(ok, only, rs, pn, pe, pb, hb, ods, ots):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      ok_pins(Up.deps.walk(rs, only, M.hub.or(hb), ods), Up.tools.walk(rs, only, ots), rs,
        pn, pe, pb, hb, ods, ots)

# LAW: every decision `ez lock --upgrade` makes writes only ez.toml over the
# ledger it renders and `.gitignore` as `I.sync` makes it
law ok_next:
  for +only: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  ok.next(Up.next(only, r, rs), Laws.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_next(only, r, rs):
  match r:
    case M.Bad{_why}:
      Unit{}
    case M.Good{m}:
      match m:
        case M.Manifest{+pn, +pe, +pb, +hb, +ods, +ots}:
          ok_known(Bool.or(U.known(only, ods), M.tool.known(only, ots)), only, rs,
            pn, pe, pb, hb, ods, ots)

# LAW: and so does every decision `ez lock` makes on a World, plain or not
law ok_world:
  for +args: W.Args
  for +ledger: Maybe<&2, String>
  for +ups: List<&2, Up.Reply>
  ok.next(W.next(args, ledger, ups), Laws.ignore.said(Up.text.said(ups, Up.Ignore{})))

def ok_world(args, ledger, ups):
  match args:
    case W.Args{up, +only}:
      match up:
        case False{}:
          Unit{}
        case True{}:
          ok_next(only, W.parsed(ledger), ups)

# The plan's writes. A write to another path leaves a path as it was; the
# upgrade's own files are ez.toml and `.gitignore` alone; and the sources are
# written after them, each once.

# the type that is empty where a path was written
def wrote.emp(w: P.Wrote) -> Type:
  match w:
    case P.Kept{}:
      Unit
    case P.Put{_t}:
      Empty

# the text a path was written with, "" when it was not
def wrote.text(w: P.Wrote) -> String:
  match w:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# LAW: a path left as it was is not a path written
law kept_put:
  for +t: String
  for e: {P.Kept{} == P.Put{t} : P.Wrote}
  Empty

def kept_put(_t, e):
  %e : wrote.emp(_)
  Unit{}

# LAW: a write to another path leaves a path as it was
law put_one_other:
  for +a: String
  for +t: String
  for +p: String
  for r: P.Wrote
  for ne: {String.eq(a, p) == False{} : Bool}
  {P.put.one(P.Write{a, t}, p, r) == r : P.Wrote}

def put_one_other(a, t, p, r, ne):
  match r:
    case P.Kept{}:
      %Equal.sym(Bool, String.eq(a, p), False{}, ne)
        : {Bool.pick(P.Wrote, _, P.Put{t}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}
    case P.Put{x}:
      {==}

# LAW: none of the upgrade's own files is at a path that is neither ez.toml
# nor `.gitignore`
law ok_go_empty:
  for a: Bool
  for b: Bool
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  for h: ok.go(a, b, t, vs, model, ig)
  Empty

def ok_go_empty(a, b, _t, _vs, _model, _ig, ea, eb, h):
  match a b:
    case True{} _:
      Eq.bit.absurd2(&1, Empty, ea)
    case False{} True{}:
      Eq.bit.absurd2(&1, Empty, eb)
    case False{} False{}:
      h

# LAW: one of the upgrade's own files, with how its path compares to another
# given as a parameter: it is not at a path that is neither of its two
law other_ne:
  for +q: String
  for +p: String
  for c: Bool
  for +ec: {String.eq(q, p) == c : Bool}
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t, vs, model, ig)
  for +n1: {String.eq(p, "ez.toml") == False{} : Bool}
  for +n2: {String.eq(p, ".gitignore") == False{} : Bool}
  {String.eq(q, p) == False{} : Bool}

def other_ne(q, p, c, ec, t, vs, model, ig, h, n1, n2):
  match c:
    case False{}:
      ec
    case True{}:
      Empty.absurd({String.eq(q, p) == False{} : Bool},
        ok_go_empty(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t, vs, model, ig,
          Equal.trans(Bool, String.eq(q, "ez.toml"), String.eq(p, "ez.toml"), False{},
            Equal.cong(String, Bool, x => String.eq(x, "ez.toml"), q, p,
              Str.string_eq_true(q, p, ec)), n1),
          Equal.trans(Bool, String.eq(q, ".gitignore"), String.eq(p, ".gitignore"), False{},
            Equal.cong(String, Bool, x => String.eq(x, ".gitignore"), q, p,
              Str.string_eq_true(q, p, ec)), n2),
          h))

# LAW: the upgrade's own files leave every other path as it was
law edits_other:
  for es: List<&2, Up.Edit>
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.edits(es, vs, model, ig)
  for +rest: List<&2, P.Effect>
  for +p: String
  for +n1: {String.eq(p, "ez.toml") == False{} : Bool}
  for +n2: {String.eq(p, ".gitignore") == False{} : Bool}
  {P.put.in(P.edits.of(es, rest), p) == P.put.in(rest, p) : P.Wrote}

def edits_other(es, vs, model, ig, h, rest, p, n1, n2):
  match es:
    case []:
      {==}
    case Up.Edit{+q, +t} <> +tl:
      (h1, h2) = h
      Equal.trans(P.Wrote,
        P.put.one(P.Write{q, t}, p, P.put.in(P.edits.of(tl, rest), p)),
        P.put.in(P.edits.of(tl, rest), p),
        P.put.in(rest, p),
        put_one_other(q, t, p, P.put.in(P.edits.of(tl, rest), p),
          other_ne(q, p, String.eq(q, p), {==}, t, vs, model, ig, h1, n1, n2)),
        edits_other(tl, vs, model, ig, h2, rest, p, n1, n2))

# LAW: a `.gitignore` the upgrade writes is one of its own files'
law ok_go_ign:
  for a: Bool
  for b: Bool
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for ea: {a == False{} : Bool}
  for eb: {b == True{} : Bool}
  for h: ok.go(a, b, t, vs, model, ig)
  {Str.clear.all(vs, '\n') == True{} : Bool} ->
    ({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
      {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>})

def ok_go_ign(a, b, t, vs, _model, ig, ea, eb, h):
  match a b:
    case True{} _:
      Eq.bit.absurd2(&1, {Str.clear.all(vs, '\n') == True{} : Bool} ->
        ({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
          {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}), ea)
    case False{} True{}:
      h
    case False{} False{}:
      Eq.bit.absurd(&1, {Str.clear.all(vs, '\n') == True{} : Bool} ->
        ({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
          {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}), eb)

# LAW: one of the upgrade's own files, with whether it is at `.gitignore`
# given as a parameter, written where nothing after it writes `.gitignore`
law ign_kept:
  for c: Bool
  for +q: String
  for +t2: String
  for +t: String
  for +ec: {String.eq(q, ".gitignore") == c : Bool}
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {Bool.pick(P.Wrote, c, P.Put{t2}, P.Kept{}) == P.Put{t} : P.Wrote}
  for +ev: {Str.clear.all(vs, '\n') == True{} : Bool}
  {I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
    {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}

def ign_kept(c, q, t2, t, ec, vs, model, ig, h, e, ev):
  match c:
    case False{}:
      Empty.absurd({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
        {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>},
        kept_put(t, e))
    case True{}:
      %Equal.cong(P.Wrote, String, x => wrote.text(x), P.Put{t2}, P.Put{t}, e)
        : {I.hashes(I.file.lines(_)) == vs : List<&2, String>} &
          {I.others(I.file.lines(_)) == I.others(I.file.lines(ig)) : List<&2, String>}
      ok_go_ign(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig,
        Equal.trans(Bool, String.eq(q, "ez.toml"), String.eq(".gitignore", "ez.toml"), False{},
          Equal.cong(String, Bool, x => String.eq(x, "ez.toml"), q, ".gitignore",
            Str.string_eq_true(q, ".gitignore", ec)), {==}),
        ec, h)(ev)

# LAW: one of the upgrade's own files in front of the rest, with what the rest
# leaves at `.gitignore` given as a parameter
law ign_arm:
  for r: P.Wrote
  for +q: String
  for +t2: String
  for +rr: P.Wrote
  for er: {rr == r : P.Wrote}
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {P.put.one(P.Write{q, t2}, ".gitignore", r) == P.Put{t} : P.Wrote}
  for ih: {rr == P.Put{t} : P.Wrote} ->
    ({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
      {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>})
  for +ev: {Str.clear.all(vs, '\n') == True{} : Bool}
  {I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
    {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}

def ign_arm(r, q, t2, rr, er, t, vs, model, ig, h, e, ih, ev):
  match r:
    case P.Put{x}:
      ih(Equal.trans(P.Wrote, rr, P.Put{x}, P.Put{t}, er, e))
    case P.Kept{}:
      ign_kept(String.eq(q, ".gitignore"), q, t2, t, {==}, vs, model, ig, h, e, ev)

# LAW: the `.gitignore` the upgrade writes, where nothing after its own files
# writes one, has the allowlist of the hashes it commits and keeps the lines
# of the file it read that are not ez's
law edits_ign:
  for es: List<&2, Up.Edit>
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.edits(es, vs, model, ig)
  for +rest: List<&2, P.Effect>
  for +kr: {P.put.in(rest, ".gitignore") == P.Kept{} : P.Wrote}
  for +t: String
  for e: {P.put.in(P.edits.of(es, rest), ".gitignore") == P.Put{t} : P.Wrote}
  for +ev: {Str.clear.all(vs, '\n') == True{} : Bool}
  {I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
    {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}

def edits_ign(es, vs, model, ig, h, rest, kr, t, e, ev):
  match es:
    case []:
      Empty.absurd({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
        {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>},
        kept_put(t, Equal.trans(P.Wrote, P.Kept{}, P.put.in(rest, ".gitignore"), P.Put{t},
          Equal.sym(P.Wrote, P.put.in(rest, ".gitignore"), P.Kept{}, kr), e)))
    case Up.Edit{+q, +t2} <> +tl:
      (h1, h2) = h
      ign_arm(P.put.in(P.edits.of(tl, rest), ".gitignore"), q, t2,
        P.put.in(P.edits.of(tl, rest), ".gitignore"), {==}, t, vs, model, ig, h1, e,
        x => edits_ign(tl, vs, model, ig, h2, rest, kr, t, x, ev), ev)

# LAW: an ez.toml the upgrade writes is one of its own files'
law ok_go_toml:
  for a: Bool
  for b: Bool
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for ea: {a == True{} : Bool}
  for h: ok.go(a, b, t, vs, model, ig)
  {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}

def ok_go_toml(a, b, _t, vs, model, _ig, ea, h):
  match a b:
    case True{} _:
      h
    case False{} True{}:
      Eq.bit.absurd(&2, {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}, ea)
    case False{} False{}:
      Eq.bit.absurd(&2, {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}, ea)

law toml_kept:
  for c: Bool
  for +q: String
  for +t2: String
  for +t: String
  for +ec: {String.eq(q, "ez.toml") == c : Bool}
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {Bool.pick(P.Wrote, c, P.Put{t2}, P.Kept{}) == P.Put{t} : P.Wrote}
  {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}

def toml_kept(c, q, t2, t, ec, vs, model, ig, h, e):
  match c:
    case False{}:
      Empty.absurd({vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>},
        kept_put(t, e))
    case True{}:
      ok_go_toml(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig,
        ec, h)

law toml_arm:
  for r: P.Wrote
  for +q: String
  for +t2: String
  for +rr: P.Wrote
  for er: {rr == r : P.Wrote}
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {P.put.one(P.Write{q, t2}, "ez.toml", r) == P.Put{t} : P.Wrote}
  for ih: {rr == P.Put{t} : P.Wrote} ->
    {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}
  {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}

def toml_arm(r, q, t2, rr, er, t, vs, model, ig, h, e, ih):
  match r:
    case P.Put{x}:
      ih(Equal.trans(P.Wrote, rr, P.Put{x}, P.Put{t}, er, e))
    case P.Kept{}:
      toml_kept(String.eq(q, "ez.toml"), q, t2, t, {==}, vs, model, ig, h, e)

# LAW: an ez.toml the upgrade writes, where nothing after its own files
# writes one, goes with the hashes the ledger it renders vends
law edits_toml:
  for es: List<&2, Up.Edit>
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: ok.edits(es, vs, model, ig)
  for +rest: List<&2, P.Effect>
  for +kr: {P.put.in(rest, "ez.toml") == P.Kept{} : P.Wrote}
  for +t: String
  for e: {P.put.in(P.edits.of(es, rest), "ez.toml") == P.Put{t} : P.Wrote}
  {vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>}

def edits_toml(es, vs, model, ig, h, rest, kr, t, e):
  match es:
    case []:
      Empty.absurd({vs == I.vended(Laws.ledger.deps(model)) : List<&2, String>},
        kept_put(t, Equal.trans(P.Wrote, P.Kept{}, P.put.in(rest, "ez.toml"), P.Put{t},
          Equal.sym(P.Wrote, P.put.in(rest, "ez.toml"), P.Kept{}, kr), e)))
    case Up.Edit{+q, +t2} <> +tl:
      (h1, h2) = h
      toml_arm(P.put.in(P.edits.of(tl, rest), "ez.toml"), q, t2,
        P.put.in(P.edits.of(tl, rest), "ez.toml"), {==}, t, vs, model, ig, h1, e,
        x => edits_toml(tl, vs, model, ig, h2, rest, kr, t, x))

# The sources. Each is written only when the moves change it.

# LAW: one source, with whether the moves change it given as a parameter:
# written at its own path, or not written
law src_miss.arm:
  for b: Bool
  for +a: String
  for +m: String
  for +es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  for +p: String
  for ne: {String.eq(a, p) == False{} : Bool}
  {P.put.in(P.edits.of(Up.edit.if(b, a, m, es), rest), p)
    == P.put.in(P.edits.of(es, rest), p) : P.Wrote}

def src_miss.arm(b, a, m, es, rest, p, ne):
  match b:
    case True{}:
      {==}
    case False{}:
      put_one_other(a, m, p, P.put.in(P.edits.of(es, rest), p), ne)

# LAW: sources none of which is at a path leave it as it was
law src_miss:
  for fs: List<&2, Up.Found>
  for +sw: List<&2, U.Swap>
  for +rest: List<&2, P.Effect>
  for +p: String
  for +m: {Laws.found.miss(fs, p) == True{} : Bool}
  {P.put.in(P.edits.of(Up.edit.sources(fs, sw), rest), p) == P.put.in(rest, p) : P.Wrote}

def src_miss(fs, sw, rest, p, m):
  match fs:
    case []:
      {==}
    case Up.Found{+a, +x} <> +tl:
      Equal.trans(P.Wrote,
        P.put.in(P.edits.of(Up.edit.if(String.eq(U.reimport.many(sw, x), x), a,
          U.reimport.many(sw, x), Up.edit.sources(tl, sw)), rest), p),
        P.put.in(P.edits.of(Up.edit.sources(tl, sw), rest), p),
        P.put.in(rest, p),
        src_miss.arm(String.eq(U.reimport.many(sw, x), x), a, U.reimport.many(sw, x),
          Up.edit.sources(tl, sw), rest, p,
          Eq.not.true(String.eq(a, p),
            Eq.and.left(Bool.not(String.eq(a, p)), Laws.found.miss(tl, p), m))),
        src_miss(tl, sw, rest, p,
          Eq.and.right(Bool.not(String.eq(a, p)), Laws.found.miss(tl, p), m)))

# LAW: sources in front of one, none of which is at its path, leave what it
# gets as it is
law src_pre:
  for pre: List<&2, Up.Found>
  for +xs: List<&2, Up.Found>
  for +sw: List<&2, U.Swap>
  for +rest: List<&2, P.Effect>
  for +p: String
  for +m: {Laws.found.miss(pre, p) == True{} : Bool}
  {P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, pre, xs), sw), rest), p)
    == P.put.in(P.edits.of(Up.edit.sources(xs, sw), rest), p) : P.Wrote}

def src_pre(pre, xs, sw, rest, p, m):
  match pre:
    case []:
      {==}
    case Up.Found{+a, +x} <> +tl:
      Equal.trans(P.Wrote,
        P.put.in(P.edits.of(Up.edit.if(String.eq(U.reimport.many(sw, x), x), a,
          U.reimport.many(sw, x), Up.edit.sources(List.append(&2, Up.Found, tl, xs), sw)),
          rest), p),
        P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, tl, xs), sw), rest), p),
        P.put.in(P.edits.of(Up.edit.sources(xs, sw), rest), p),
        src_miss.arm(String.eq(U.reimport.many(sw, x), x), a, U.reimport.many(sw, x),
          Up.edit.sources(List.append(&2, Up.Found, tl, xs), sw), rest, p,
          Eq.not.true(String.eq(a, p),
            Eq.and.left(Bool.not(String.eq(a, p)), Laws.found.miss(tl, p), m))),
        src_pre(tl, xs, sw, rest, p,
          Eq.and.right(Bool.not(String.eq(a, p)), Laws.found.miss(tl, p), m)))

# what a source leaves at its path: nothing when the moves left its text as
# it was, and the rewritten text otherwise. Law vocabulary: ez never calls it.
def wrote.of(same: Bool, +t: String) -> P.Wrote:
  match same:
    case True{}:
      P.Kept{}
    case False{}:
      P.Put{t}

# LAW: one source, with whether the moves change it given as a parameter,
# written where nothing after it writes its path
law src_one.arm:
  for b: Bool
  for +at: String
  for +m: String
  for +es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  for kr: {P.put.in(P.edits.of(es, rest), at) == P.Kept{} : P.Wrote}
  {P.put.in(P.edits.of(Up.edit.if(b, at, m, es), rest), at) == wrote.of(b, m) : P.Wrote}

def src_one.arm(b, at, m, es, rest, kr):
  match b:
    case True{}:
      kr
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.edits.of(es, rest), at), P.Kept{}, kr)
        : {P.put.one(P.Write{at, m}, at, _) == P.Put{m} : P.Wrote}
      %Equal.sym(Bool, String.eq(at, at), True{}, Eq.string_eq_self(at))
        : {Bool.pick(P.Wrote, _, P.Put{m}, P.Kept{}) == P.Put{m} : P.Wrote}
      {==}

# LAW: a source the World names once is written with its text rewritten, or
# not written when the moves leave it as it was
law src_all:
  for +pre: List<&2, Up.Found>
  for +at: String
  for +text: String
  for +post: List<&2, Up.Found>
  for +sw: List<&2, U.Swap>
  for +rest: List<&2, P.Effect>
  for +mp: {Laws.found.miss(pre, at) == True{} : Bool}
  for +mq: {Laws.found.miss(post, at) == True{} : Bool}
  for +kr: {P.put.in(rest, at) == P.Kept{} : P.Wrote}
  {P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, pre,
    Up.Found{at, text} <> post), sw), rest), at)
    == wrote.of(String.eq(U.reimport.many(sw, text), text), U.reimport.many(sw, text))
    : P.Wrote}

def src_all(pre, at, text, post, sw, rest, mp, mq, kr):
  Equal.trans(P.Wrote,
    P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, pre,
      Up.Found{at, text} <> post), sw), rest), at),
    P.put.in(P.edits.of(Up.edit.sources(Up.Found{at, text} <> post, sw), rest), at),
    wrote.of(String.eq(U.reimport.many(sw, text), text), U.reimport.many(sw, text)),
    src_pre(pre, Up.Found{at, text} <> post, sw, rest, at, mp),
    src_one.arm(String.eq(U.reimport.many(sw, text), text), at, U.reimport.many(sw, text),
      Up.edit.sources(post, sw), rest,
      Equal.trans(P.Wrote, P.put.in(P.edits.of(Up.edit.sources(post, sw), rest), at),
        P.put.in(rest, at), P.Kept{}, src_miss(post, sw, rest, at, mq), kr)))

# LAW: a path that ends `.bend` is none of the paths that do not, with how
# they compare given as a parameter
law not_bend.arm:
  for +lit: String
  for +at: String
  for c: Bool
  for ec: {String.eq(at, lit) == c : Bool}
  for lb: {String.ends_with(lit, ".bend") == False{} : Bool}
  for bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {String.eq(at, lit) == False{} : Bool}

def not_bend.arm(lit, at, c, ec, lb, bend):
  match c:
    case False{}:
      ec
    case True{}:
      Eq.bit.absurd2(&2, {String.eq(at, lit) == False{} : Bool},
        Equal.trans(Bool, True{}, String.ends_with(lit, ".bend"), False{},
          Equal.trans(Bool, True{}, String.ends_with(at, ".bend"), String.ends_with(lit, ".bend"),
            Equal.sym(Bool, String.ends_with(at, ".bend"), True{}, bend),
            Equal.cong(String, Bool, x => String.ends_with(x, ".bend"), at, lit,
              Str.string_eq_true(at, lit, ec))),
          lb))

law not_bend:
  for +lit: String
  for +at: String
  for lb: {String.ends_with(lit, ".bend") == False{} : Bool}
  for bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {String.eq(at, lit) == False{} : Bool}

def not_bend(lit, at, lb, bend):
  not_bend.arm(lit, at, String.eq(at, lit), {==}, lb, bend)

# LAW: and the other way round
law not_bend.flip:
  for +lit: String
  for +at: String
  for lb: {String.ends_with(lit, ".bend") == False{} : Bool}
  for bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {String.eq(lit, at) == False{} : Bool}

def not_bend.flip(lit, at, lb, bend):
  MP.eq_flip(at, lit, not_bend(lit, at, lb, bend))

# LAW: the lock, written last, is not at a source's path
law lock_kept:
  for +at: String
  for +lt: String
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {P.put.in([P.Write{P.lockfile(), lt}], at) == P.Kept{} : P.Wrote}

def lock_kept(at, lt, bend):
  put_one_other("ez.lock.toml", lt, at, P.Kept{}, not_bend.flip("ez.lock.toml", at, {==}, bend))

# LAW: the sources' writes, and the lock after them, leave at a source's path
# the World names once what its own write leaves
law src_after:
  for +nx: Up.Next
  for +lt: String
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {Laws.found.miss(pre, at) == True{} : Bool}
  for +mq: {Laws.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at)
    == wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
      U.reimport.many(Up.next.swaps(nx), text)) : P.Wrote}

def src_after(nx, lt, at, text, pre, post, efs, mp, mq, bend):
  %Equal.sym(List<&2, Up.Found>, Up.next.found(nx),
    List.append(&2, Up.Found, pre, Up.Found{at, text} <> post), efs)
    : {P.put.in(P.edits.of(Up.edit.sources(_, Up.next.swaps(nx)),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at)
      == wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
        U.reimport.many(Up.next.swaps(nx), text)) : P.Wrote}
  src_all(pre, at, text, post, Up.next.swaps(nx),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), mp, mq,
    Equal.trans(P.Wrote,
      P.put.in(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), at),
      P.put.in([P.Write{P.lockfile(), lt}], at),
      P.Kept{},
      drops_put(Up.next.drops(nx), [P.Write{P.lockfile(), lt}], at),
      lock_kept(at, lt, bend)))

# LAW: a made plan leaves at a source's path what the sources' writes leave
# there
law made_src:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +lt: String
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for +ig: String
  for okn: ok.next(nx, ig)
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {Laws.found.miss(pre, at) == True{} : Bool}
  for +mq: {Laws.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {P.put.plan(P.made(nx, cs, js, P.Doc{lt}), at)
    == wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
      U.reimport.many(Up.next.swaps(nx), text)) : P.Wrote}

def made_src(nx, cs, js, lt, at, text, pre, post, ig, okn, efs, mp, mq, bend):
  Equal.trans(P.Wrote,
    P.put.in(P.says.of(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js,
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), at),
    P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
      Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at),
    wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
      U.reimport.many(Up.next.swaps(nx), text)),
    Equal.trans(P.Wrote,
      P.put.in(P.says.of(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js,
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), at),
      P.put.in(P.lays(cs, Up.next.vends(nx), js,
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))), at),
      P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at),
      says_put(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js,
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))), at),
      lays_put(cs, Up.next.vends(nx), js,
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at)),
    Equal.trans(P.Wrote,
      P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at),
      P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at),
      wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
        U.reimport.many(Up.next.swaps(nx), text)),
      edits_other(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig, okn,
        P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
          P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at,
        not_bend("ez.toml", at, {==}, bend), not_bend(".gitignore", at, {==}, bend)),
      src_after(nx, lt, at, text, pre, post, efs, mp, mq, bend)))

# LAW: what a source leaves, rewritten or not written, is its rewritten text
law left_of:
  for b: Bool
  for +m: String
  for +text: String
  for eb: {String.eq(m, text) == b : Bool}
  {Laws.left.at(wrote.of(b, m), text) == m : String}

def left_of(b, m, text, eb):
  match b:
    case True{}:
      Equal.sym(String, m, text, Str.string_eq_true(m, text, eb))
    case False{}:
      {==}

# LAW: a plan that is made leaves at a `.bend` source the World names once its
# text with every moved hash rewritten; a refusal is not made
law rw_arm:
  for d: P.Doc
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for +ig: String
  for okn: ok.next(nx, ig)
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {Laws.found.miss(pre, at) == True{} : Bool}
  for +mq: {Laws.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses.doc(d) == False{} : Bool}
  {Laws.left.at(P.put.plan(P.made(nx, cs, js, d), at), text)
    == U.reimport.many(Up.next.swaps(nx), text) : String}

def rw_arm(d, nx, cs, js, at, text, pre, post, ig, okn, efs, mp, mq, bend, ok):
  match d:
    case P.Stop{_why}:
      Eq.bit.absurd2(&2, {Laws.left.at(P.Kept{}, text) == U.reimport.many(Up.next.swaps(nx), text)
        : String}, ok)
    case P.Doc{+lt}:
      %Equal.sym(P.Wrote, P.put.plan(P.made(nx, cs, js, P.Doc{lt}), at),
        wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
          U.reimport.many(Up.next.swaps(nx), text)),
        made_src(nx, cs, js, lt, at, text, pre, post, ig, okn, efs, mp, mq, bend))
        : {Laws.left.at(_, text) == U.reimport.many(Up.next.swaps(nx), text) : String}
      left_of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
        U.reimport.many(Up.next.swaps(nx), text), text, {==})

def Laws.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      rw_arm(P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        at, text, pre, post, Laws.ignore.said(Up.text.said(ups, Up.Ignore{})),
        ok_world(args, ledger, ups), fs, mp, mq, bend, ok)

def Laws.upgrade_rewrites_imports(
  w,
  at,
  text,
  pre,
  post,
  fs,
  mp,
  mq,
  bend,
  ok,
  i,
  old,
  new,
  mv,
  to,
  hit
):
  %Equal.sym(String, Laws.left.at(P.put(w, at), text), U.reimport.many(Laws.swaps(w), text),
    Laws.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok))
    : {String.starts_with(ML.line.at(String.lines(_), i), U.reimport.head(new)) == True{} : Bool}
  ML.rewrite_names_new(Laws.swaps(w), text, i, old, new, mv, to, hit)

def Laws.upgrade_leaves_other_lines(w, at, text, pre, post, fs, mp, mq, bend, ok, i, mv, miss):
  %Equal.sym(String, Laws.left.at(P.put(w, at), text), U.reimport.many(Laws.swaps(w), text),
    Laws.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok))
    : {ML.line.at(String.lines(_), i) == ML.line.at(String.lines(text), i) : String}
  ML.rewrite_keeps_other_lines(Laws.swaps(w), text, i, mv, miss)

def Laws.upgrade_keeps_line_count(w, at, text, pre, post, fs, mp, mq, bend, ok, mv):
  %Equal.sym(String, Laws.left.at(P.put(w, at), text), U.reimport.many(Laws.swaps(w), text),
    Laws.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok))
    : {List.length(&2, String, String.lines(_))
      == List.length(&2, String, String.lines(text)) : Nat}
  ML.rewrite_keeps_line_count(Laws.swaps(w), text, mv)

# LAW: a source the moves leave as it was is not written
law kept_of:
  for +m: String
  for +text: String
  for +e: {m == text : String}
  {wrote.of(String.eq(m, text), m) == P.Kept{} : P.Wrote}

def kept_of(m, text, e):
  %Equal.sym(String, m, text, e) : {wrote.of(String.eq(_, text), _) == P.Kept{} : P.Wrote}
  %Equal.sym(Bool, String.eq(text, text), True{}, Eq.string_eq_self(text))
    : {wrote.of(_, text) == P.Kept{} : P.Wrote}
  {==}

# LAW: a plan leaves a source none of whose lines names a moved hash
# unwritten, whether it is made or refused
law hits_arm:
  for d: P.Doc
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for +ig: String
  for okn: ok.next(nx, ig)
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {Laws.found.miss(pre, at) == True{} : Bool}
  for +mq: {Laws.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for none: {ML.names.none.all(Up.next.swaps(nx), String.lines(text)) == True{} : Bool}
  {P.put.plan(P.made(nx, cs, js, d), at) == P.Kept{} : P.Wrote}

def hits_arm(d, nx, cs, js, at, text, pre, post, ig, okn, efs, mp, mq, bend, none):
  match d:
    case P.Stop{_why}:
      {==}
    case P.Doc{+lt}:
      Equal.trans(P.Wrote,
        P.put.plan(P.made(nx, cs, js, P.Doc{lt}), at),
        wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
          U.reimport.many(Up.next.swaps(nx), text)),
        P.Kept{},
        made_src(nx, cs, js, lt, at, text, pre, post, ig, okn, efs, mp, mq, bend),
        kept_of(U.reimport.many(Up.next.swaps(nx), text), text,
          ML.rewrite_nothing_named(Up.next.swaps(nx), text, none)))

def Laws.upgrade_writes_only_hits(w, at, text, pre, post, fs, mp, mq, bend, none):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      hits_arm(P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        at, text, pre, post, Laws.ignore.said(Up.text.said(ups, Up.Ignore{})),
        ok_world(args, ledger, ups), fs, mp, mq, bend, none)

# LAW: a made plan's writes after the upgrade's own files, the sources and
# the lock, leave `.gitignore` and ez.toml as they were, when no source is at
# either
law rest_kept:
  for +nx: Up.Next
  for +lt: String
  for +p: String
  for m: {Laws.found.miss(Up.next.found(nx), p) == True{} : Bool}
  for lk: {P.put.in([P.Write{P.lockfile(), lt}], p) == P.Kept{} : P.Wrote}
  {P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), p) == P.Kept{} : P.Wrote}

def rest_kept(nx, lt, p, m, lk):
  Equal.trans(P.Wrote,
    P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), p),
    P.put.in(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), p),
    P.Kept{},
    src_miss(Up.next.found(nx), Up.next.swaps(nx),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), p, m),
    Equal.trans(P.Wrote,
      P.put.in(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), p),
      P.put.in([P.Write{P.lockfile(), lt}], p),
      P.Kept{},
      drops_put(Up.next.drops(nx), [P.Write{P.lockfile(), lt}], p),
      lk))

# LAW: a made plan leaves at a path what the upgrade's own files and what
# follows them leave there
law made_edits:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +lt: String
  for +p: String
  {P.put.plan(P.made(nx, cs, js, P.Doc{lt}), p)
    == P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
      Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), p)
    : P.Wrote}

def made_edits(nx, cs, js, lt, p):
  Equal.trans(P.Wrote,
    P.put.in(P.says.of(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js,
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), p),
    P.put.in(P.lays(cs, Up.next.vends(nx), js,
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))), p),
    P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
      Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), p),
    says_put(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js,
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))), p),
    lays_put(cs, Up.next.vends(nx), js,
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), p))

# LAW: the `.gitignore` a plan writes, when no source is at it, has the
# allowlist of the hashes the upgrade commits and keeps the lines of the file
# it read that are not ez's
law ign_plan:
  for d: P.Doc
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +t: String
  for e: {P.put.plan(P.made(nx, cs, js, d), ".gitignore") == P.Put{t} : P.Wrote}
  for +miss: {Laws.found.miss(Up.next.found(nx), ".gitignore") == True{} : Bool}
  for +ig: String
  for okn: ok.next(nx, ig)
  for +ev: {Str.clear.all(Up.next.vends(nx), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(t)) == Up.next.vends(nx) : List<&2, String>} &
    {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}

def ign_plan(d, nx, cs, js, t, e, miss, ig, okn, ev):
  match d:
    case P.Stop{_why}:
      Empty.absurd({I.hashes(I.file.lines(t)) == Up.next.vends(nx) : List<&2, String>} &
        {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>},
        kept_put(t, e))
    case P.Doc{+lt}:
      edits_ign(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig, okn,
        P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
          P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])),
        rest_kept(nx, lt, ".gitignore", miss, {==}), t,
        Equal.trans(P.Wrote,
          P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
            Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))),
            ".gitignore"),
          P.put.plan(P.made(nx, cs, js, P.Doc{lt}), ".gitignore"),
          P.Put{t},
          Equal.sym(P.Wrote, P.put.plan(P.made(nx, cs, js, P.Doc{lt}), ".gitignore"),
            P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
              Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))),
              ".gitignore"),
            made_edits(nx, cs, js, lt, ".gitignore")),
          e),
        ev)

# the `.gitignore` facts on a World
law ign_world:
  for +w: W.World
  for +text: String
  for put: {P.put(w, ".gitignore") == P.Put{text} : P.Wrote}
  for +miss: {Laws.found.miss(Laws.found(w), ".gitignore") == True{} : Bool}
  for +ev: {Str.clear.all(Laws.vends(w), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(text)) == Laws.vends(w) : List<&2, String>} &
    {I.others(I.file.lines(text)) == I.others(I.file.lines(Laws.ignore.read(w)))
      : List<&2, String>}

def ign_world(w, text, put, miss, ev):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      ign_plan(P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        text, put, miss, Laws.ignore.said(Up.text.said(ups, Up.Ignore{})),
        ok_world(args, ledger, ups), ev)

# the first of two facts
def fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, _b) = p
  a

# the second
def snd(-A: Type, -B: Type, p: A & B) -> B:
  (_a, b) = p
  b

def Laws.upgrade_allowlist_is_the_ledger(w, text, put, miss, ev):
  fst({I.hashes(I.file.lines(text)) == Laws.vends(w) : List<&2, String>},
    {I.others(I.file.lines(text)) == I.others(I.file.lines(Laws.ignore.read(w)))
      : List<&2, String>},
    ign_world(w, text, put, miss, ev))

def Laws.upgrade_allowlist_keeps_other_lines(w, text, put, miss, ev):
  snd({I.hashes(I.file.lines(text)) == Laws.vends(w) : List<&2, String>},
    {I.others(I.file.lines(text)) == I.others(I.file.lines(Laws.ignore.read(w)))
      : List<&2, String>},
    ign_world(w, text, put, miss, ev))

# LAW: the ez.toml a plan writes, when no source is at it, goes with the
# hashes of the ledger it renders
law toml_plan:
  for d: P.Doc
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +t: String
  for e: {P.put.plan(P.made(nx, cs, js, d), "ez.toml") == P.Put{t} : P.Wrote}
  for +miss: {Laws.found.miss(Up.next.found(nx), "ez.toml") == True{} : Bool}
  for +ig: String
  for okn: ok.next(nx, ig)
  {Up.next.vends(nx) == I.vended(Laws.ledger.deps(Up.next.model(nx))) : List<&2, String>}

def toml_plan(d, nx, cs, js, t, e, miss, ig, okn):
  match d:
    case P.Stop{_why}:
      Empty.absurd({Up.next.vends(nx) == I.vended(Laws.ledger.deps(Up.next.model(nx)))
        : List<&2, String>}, kept_put(t, e))
    case P.Doc{+lt}:
      edits_toml(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig, okn,
        P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
          P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])),
        rest_kept(nx, lt, "ez.toml", miss, {==}), t,
        Equal.trans(P.Wrote,
          P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
            Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))),
            "ez.toml"),
          P.put.plan(P.made(nx, cs, js, P.Doc{lt}), "ez.toml"),
          P.Put{t},
          Equal.sym(P.Wrote, P.put.plan(P.made(nx, cs, js, P.Doc{lt}), "ez.toml"),
            P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
              Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))),
              "ez.toml"),
            made_edits(nx, cs, js, lt, "ez.toml")),
          e))

def Laws.upgrade_vends_the_ledger(w, text, put, miss):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      toml_plan(P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        text, put, miss, Laws.ignore.said(Up.text.said(ups, Up.Ignore{})),
        ok_world(args, ledger, ups))
# The upgrade's moves (EZ-RES-5, EZ-RES-8). Each law is one fact about one
# dependency's fate (`Up.dep.one`), carried through the walk over the ledger's
# dependencies (`Up.deps.walk`) to the ledger model the upgrade renders
# (`Up.next.model`). A fate is proved sound once for any remote tip, since a
# tag's and the default branch's are read the same way from there on
# (`Up.dep.tip`).

# a pin from a repository, with its fields spelled out
def mv.git(
  +hn: String,
  +hh: String,
  +he: String,
  +url: String,
  +rev: String,
  +tag: String,
  +root: String,
  +nar: String,
  +vend: Bool
) -> M.Dep:
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

def mv.ok_hub(
  hb,
  rs,
  _hn,
  _hh,
  _he,
  url,
  rev,
  tag,
  _root,
  _nar,
  _vend,
  _hash,
  r,
  _tg,
  _br,
  _root2,
  _nar2,
  _man,
  _srcs,
  e
):
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

def mv.fine_one(am, rs, _only, hub, h):
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
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, _, _, _} Up.Deps{+ds, _, _, _, _, _, +asks, +bad}:
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
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, _, _, _} Up.Deps{+ds, _, _, _, _, _, +asks, +bad}:
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

def mv.model_srcs(
  srcs,
  t,
  rs,
  n,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  _ss,
  _es,
  dm,
  _dsy,
  _dtr,
  tts,
  tm,
  _tsy,
  _ig,
  wk,
  self
):
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

def mv.model_ignore(
  said,
  srcs,
  t,
  rs,
  n,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  ss,
  es,
  dm,
  dsy,
  dtr,
  tts,
  tm,
  tsy,
  wk,
  self
):
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

def mv.tip_drift(
  rs,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  tag,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  nar2,
  root2,
  man,
  srcs,
  same,
  co,
  drift
):
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

def mv.fwd_off_sel(
  s,
  rs,
  _only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  sel,
  head,
  moved,
  off
):
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

def mv.fol_off_sel(
  s,
  rs,
  _only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  c,
  ct,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  sel,
  refs,
  moved,
  off
):
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

def mv.fol_drift_sel(
  s,
  rs,
  _only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  c,
  ct,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  nar2,
  root2,
  man,
  srcs,
  sel,
  refs,
  same,
  co,
  drift
):
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

def mv.fol_drift(
  rs,
  only,
  hub,
  h,
  tip,
  tg,
  br,
  nar2,
  root2,
  man,
  srcs,
  named,
  sel,
  refs,
  same,
  co,
  drift
):
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
    case Up.Became{_d, _, _, _, _, _, _} Up.Deps{_ds, _ss, _es, _any, _sy2, _tr2, _asks, bad}:
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
    case Up.Became{_d, _, _, _, _, _, _} Up.Deps{_ds, _ss, _es, _any, _sy2, _tr2, _asks, _bad}:
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

def Laws.upgrade_tag_refuses_drift(
  w,
  n,
  tip,
  tag,
  branch,
  nar,
  root,
  manifest,
  srcs,
  up,
  named,
  sel,
  refs,
  same,
  co,
  drift
):
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

def mv.live_hub(
  hb,
  _hn,
  _hh,
  _he,
  _url,
  _rev,
  _tag,
  _root,
  _nar,
  _vend,
  _hash,
  tip,
  _br,
  _root2,
  _nar2,
  _man,
  _srcs
):
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

def mv.live_agree(
  g,
  _rs,
  _hub,
  _hn,
  _hh,
  _he,
  _url,
  rev,
  _tag,
  _root,
  _nar,
  _vend,
  tip,
  _tg,
  _seen,
  e
):
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

def mv.fol_live_sel(
  s,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  c,
  ct,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  sel,
  refs
):
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

def mv.live_hit(f, rest, n, tip, hn, _hh, _he, src, e, lv, fn):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, +m, _, _} Up.Deps{+ds, _, _, +any, _, _, +asks, +bad}:
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
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, +m, _, _} Up.Deps{+ds, _, _, +any, _, _, +asks, +bad}:
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

def mv.reach_srcs(
  srcs,
  tip,
  n,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  _ss,
  _es,
  dm,
  _dsy,
  _dtr,
  tts,
  tm,
  _tsy,
  _ig,
  wk,
  se
):
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

def mv.reach_ignore(
  said,
  srcs,
  tip,
  n,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  ss,
  es,
  dm,
  dsy,
  dtr,
  tts,
  tm,
  tsy,
  wk,
  se
):
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

# ---------------------------------------------------------------------------
# EZ-DOC-4 for `ez lock --upgrade`: run again on the World it leaves, against
# a remote that did not change, it moves nothing, writes the same lock, writes
# no ledger, source or `.gitignore`, and lays nothing new. The key step is
# `kp.same` for a dependency and `tk.same` for a tool: a pin at its own tip,
# whose checkout there agrees with it, is kept. Each fate the first upgrade
# decides (`a.one`, `t.one`) is carried to the second's (`again`), each walk
# (`w.all`, `tw.all`), then the decision (`core`) and the plan.

# the answers the next upgrade reads: `.gitignore` as the last one left it,
# then the same answers
def re(g: String, rs: List<&2, Up.Reply>) -> List<&2, Up.Reply>:
  Up.Reply{Up.Ignore{}, Up.Text{g}} <> rs

# LAW: a question that is not `.gitignore` is answered past it
law re.heard:
  for +q: Up.Ask
  for g: String
  for rs: List<&2, Up.Reply>
  for ne: {String.eq("ignore", Up.key(q)) == False{} : Bool}
  {Up.heard(re(g, rs), q) == Up.heard(rs, q) : Up.Heard}

def re.heard(q, g, rs, ne):
  nes = Equal.sym(Bool, String.eq("ignore", Up.key(q)), False{}, ne)
  %nes : {Up.look.step(_, Up.Text{g}, _u => Up.look(rs, Up.key(q))) == Up.heard(rs, q) : Up.Heard}
  {==}

# LAW: what git printed for refs, past `.gitignore`
law re.refs:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +ref: String
  for +what: String
  {Up.printed(re(g, rs), Up.Refs{url, ref}, what) == Up.printed(rs, Up.Refs{url, ref}, what) : Up.Said}

def re.refs(g, rs, url, ref, what):
  Equal.cong(Up.Heard, Up.Said, h => Up.printed.heard(h, Up.Refs{url, ref}, what),
    Up.heard(re(g, rs), Up.Refs{url, ref}), Up.heard(rs, Up.Refs{url, ref}),
    re.heard(Up.Refs{url, ref}, g, rs, {==}))

law re.head:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +what: String
  {Up.printed(re(g, rs), Up.Head{url}, what) == Up.printed(rs, Up.Head{url}, what) : Up.Said}

def re.head(g, rs, url, what):
  Equal.cong(Up.Heard, Up.Said, h => Up.printed.heard(h, Up.Head{url}, what),
    Up.heard(re(g, rs), Up.Head{url}), Up.heard(rs, Up.Head{url}),
    re.heard(Up.Head{url}, g, rs, {==}))

# LAW: the commit a ref names, past `.gitignore`
law re.follow.ask:
  for b: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +ref: String
  {Up.follow.ask(b, re(g, rs), url, ref) == Up.follow.ask(b, rs, url, ref) : Up.Tip}

def re.follow.ask(b, g, rs, url, ref):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Up.Said, Up.Tip, x => Up.follow.said(x, url, ref),
        Up.printed(re(g, rs), Up.Refs{url, ref}, "ls-remote " ++ url),
        Up.printed(rs, Up.Refs{url, ref}, "ls-remote " ++ url),
        re.refs(g, rs, url, ref, "ls-remote " ++ url))

law re.follow:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +ref: String
  {Up.follow(re(g, rs), url, ref) == Up.follow(rs, url, ref) : Up.Tip}

def re.follow(g, rs, url, ref):
  re.follow.ask(Git.is_rev(ref), g, rs, url, ref)

# LAW: the default branch's tip, past `.gitignore`
law re.forward:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  {Up.forward(re(g, rs), url) == Up.forward(rs, url) : Up.Tip}

def re.forward(g, rs, url):
  Equal.cong(Up.Said, Up.Tip, x => Up.forward.said(x, url),
    Up.printed(re(g, rs), Up.Head{url}, "ls-remote " ++ url),
    Up.printed(rs, Up.Head{url}, "ls-remote " ++ url),
    re.head(g, rs, url, "ls-remote " ++ url))

# LAW: a checkout, past `.gitignore`
law re.checkout:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +rev: String
  for +entry: String
  {Up.checkout(re(g, rs), Up.Tree{url, rev, entry}) == Up.checkout(rs, Up.Tree{url, rev, entry})
    : Up.Co}

def re.checkout(g, rs, url, rev, entry):
  Equal.cong(Up.Heard, Up.Co, h => Up.checkout.heard(h, Up.Tree{url, rev, entry}),
    Up.heard(re(g, rs), Up.Tree{url, rev, entry}), Up.heard(rs, Up.Tree{url, rev, entry}),
    re.heard(Up.Tree{url, rev, entry}, g, rs, {==}))

# LAW: a weighing, past `.gitignore`
law re.weighed:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +rev: String
  {Up.weighed(re(g, rs), Up.Weigh{url, rev}) == Up.weighed(rs, Up.Weigh{url, rev}) : Up.Wd}

def re.weighed(g, rs, url, rev):
  Equal.cong(Up.Heard, Up.Wd, h => Up.weighed.heard(h, Up.Weigh{url, rev}),
    Up.heard(re(g, rs), Up.Weigh{url, rev}), Up.heard(rs, Up.Weigh{url, rev}),
    re.heard(Up.Weigh{url, rev}, g, rs, {==}))

# ---------------------------------------------------------------------------
# one dependency, upgraded again

# the tip an aim asks the remote for
def up.tip(am: U.Aim, +rs: List<&2, Up.Reply>, +url: String) -> Up.Tip:
  match am:
    case U.Hold{}:
      Up.TipNo{""}
    case U.Follow{ref}:
      Up.follow(rs, url, ref)
    case U.Forward{}:
      Up.forward(rs, url)

# whether a tip is a commit
def tip.at(t: Up.Tip) -> Bool:
  match t:
    case Up.At{_r, _t, _b}:
      True{}
    case Up.TipWait{_a}:
      False{}
    case Up.TipNo{_w}:
      False{}

# a dependency kept as it is, with the lines it says
def kept(d: M.Dep, s: List<&2, String>) -> Up.Fate:
  Up.Became{d, "", "", "", False{}, s, []}

# the lines a fate says
def fsays(f: Up.Fate) -> List<&2, String>:
  match f:
    case Up.Became{_d, _o, _n, _p, _m, s, _t}:
      s
    case Up.Waits{_a}:
      []
    case Up.Halts{_w}:
      []

# what the next upgrade makes of a dependency this one left
def again.d(+d: M.Dep, +g: String, +rs: List<&2, Up.Reply>, +only: String, +hub: String) -> Up.Fate:
  Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), re(g, rs), only, hub, d)

def again(f: Up.Fate, +g: String, +rs: List<&2, Up.Reply>, +only: String, +hub: String) -> Up.Fate:
  match f:
    case Up.Became{+d, _o, _n, _p, _m, _s, _t}:
      again.d(d, g, rs, only, hub)
    case Up.Waits{+a}:
      Up.Waits{a}
    case Up.Halts{+w}:
      Up.Halts{w}

# a fate with the pin it left kept, saying the lines given
def still(f: Up.Fate, s: List<&2, String>) -> Up.Fate:
  match f:
    case Up.Became{d, _o, _n, _p, _m, _s, _t}:
      kept(d, s)
    case Up.Waits{+a}:
      Up.Waits{a}
    case Up.Halts{+w}:
      Up.Halts{w}

# LAW: a checkout that agrees with itself
law agree_self:
  for +h: String
  for +nar: String
  for +root: String
  {U.agree(h, h, nar, nar, root, root) == True{} : Bool}

def agree_self(h, nar, root):
  eh = Equal.sym(Bool, String.eq(h, h), True{}, Eq.string_eq_self(h))
  %eh : {U.agree.go(_, String.eq(nar, nar), String.eq(root, root)) == True{} : Bool}
  en = Equal.sym(Bool, String.eq(nar, nar), True{}, Eq.string_eq_self(nar))
  %en : {U.agree.go(True{}, _, String.eq(root, root)) == True{} : Bool}
  Eq.string_eq_self(root)

# LAW: a pin at its own tip, whose checkout there agrees with it, is kept.
# This is the key step of the upgrade's idempotence.
law kp.same:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for es: {String.eq(r, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.of(man1), nr, nar1, rt, root1) == True{} : Bool}
  {Up.dep.same(String.eq(r, tip), re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
    tip, tag, br)
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.same(String.eq(r, tip), re(g, rs), hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br))) : Up.Fate}

def kp.same(g, rs, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1, srcs1, es, eco, eag):
  nes = Equal.sym(Bool, String.eq(r, tip), True{}, es)
  %nes : {Up.dep.same(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.same(_, re(g, rs), hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br))) : Up.Fate}
  eco2 = Equal.sym(Up.Co, Up.checkout(re(g, rs), Up.Tree{url, r, he}), Up.Co{nar1, root1, man1, srcs1},
    Equal.trans(Up.Co, Up.checkout(re(g, rs), Up.Tree{url, r, he}), Up.checkout(rs, Up.Tree{url, r, he}),
      Up.Co{nar1, root1, man1, srcs1}, re.checkout(g, rs, url, r, he), eco))
  %eco2 : {Up.dep.kept(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.kept(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)))
    : Up.Fate}
  nag = Equal.sym(Bool, U.agree(hh, Up.hash.of(man1), nr, nar1, rt, root1), True{}, eag)
  %nag : {Up.dep.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs), hub,
      M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, "", Up.hash.of(man1))
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs), hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, "", Up.hash.of(man1)))) : Up.Fate}
  {==}

# LAW: a tip is not a commit's absence
law tip.clash:
  for +t: Up.Tip
  for +why: String
  for e: {Up.TipNo{why} == t : Up.Tip}
  for a: {tip.at(t) == True{} : Bool}
  {False{} == True{} : Bool}

def tip.clash(t, why, e, a):
  Equal.trans(Bool, False{}, tip.at(t), True{},
    Equal.cong(Up.Tip, Bool, x => tip.at(x), Up.TipNo{why}, t, e), a)

# LAW: the same, once the aim is known
law kp.aim:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.of(man1), nr, nar1, rt, root1) == True{} : Bool}
  {Up.dep.one(am, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.one(am, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
    : Up.Fate}

def kp.aim(
  am,
  g,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  r,
  tg,
  rt,
  nr,
  vd,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  et,
  es,
  eco,
  eag
):
  match am:
    case U.Hold{}:
      Eq.bit.absurd(&2, {Up.dep.one(U.Hold{}, re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
        == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
          fsays(Up.dep.one(U.Hold{}, re(g, rs), only, hub,
            M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Fate},
        tip.clash(Up.At{tip, tag, br}, "", et, {==}))
    case U.Follow{+ref}:
      e3 = Equal.sym(Up.Tip, Up.follow(re(g, rs), url, ref), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.follow(re(g, rs), url, ref), Up.follow(rs, url, ref),
          Up.At{tip, tag, br}, re.follow(g, rs, url, ref), et))
      %e3 : {Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
        == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
          fsays(Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
        : Up.Fate}
      kp.same(g, rs, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1, srcs1,
        es, eco, eag)
    case U.Forward{}:
      e3 = Equal.sym(Up.Tip, Up.forward(re(g, rs), url), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.forward(re(g, rs), url), Up.forward(rs, url),
          Up.At{tip, tag, br}, re.forward(g, rs, url), et))
      %e3 : {Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
        == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
          fsays(Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
        : Up.Fate}
      kp.same(g, rs, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1, srcs1,
        es, eco, eag)

# LAW: the next upgrade keeps a pin that is at the tip its remote names and
# agrees with its checkout there. `ea` says the pin is asked what it was asked
# before, whatever commit, root and narHash it now records.
law kp.again:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +r0: String
  for +rt0: String
  for +nr0: String
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.of(man1), nr, nar1, rt, root1) == True{} : Bool}
  {again.d(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only, hub)
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(again.d(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only, hub))) : Up.Fate}

def kp.again(
  am,
  g,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  r,
  tg,
  rt,
  nr,
  vd,
  r0,
  rt0,
  nr0,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  ec,
  ea,
  et,
  es,
  eco,
  eag
):
  nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
  %nec : {Up.dep.one(U.aim(_, M.Git{url, r, tg, rt, nr, vd}), re(g, rs), only, hub,
      M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.one(U.aim(_, M.Git{url, r, tg, rt, nr, vd}), re(g, rs), only, hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Fate}
  nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), am, ea)
  %nea : {Up.dep.one(_, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
    == kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.one(_, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
    : Up.Fate}
  kp.aim(am, g, rs, only, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1,
    srcs1, et, es, eco, eag)


# LAW: a pin moved to the tip, once the hub has had its word, is kept by the next run
law a.hub:
  for hb: Up.Hubbed
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for eco: {Up.checkout(rs, Up.Tree{url, tip, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  {again(Up.dep.hub(hb, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, Up.hash.of(man1), tip, root1, nar1, man1,
    srcs1, br), g, rs, only, hub)
    == still(Up.dep.hub(hb, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, Up.hash.of(man1), tip, root1, nar1,
      man1, srcs1, br),
      fsays(again(Up.dep.hub(hb, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, Up.hash.of(man1), tip, root1,
        nar1, man1, srcs1, br), g, rs, only, hub))) : Up.Fate}

def a.hub(
  hb,
  g,
  rs,
  only,
  hub,
  hn,
  _hh,
  he,
  url,
  r0,
  tg,
  rt0,
  nr0,
  vd,
  am,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  ec,
  ea,
  et,
  eco
):
  match hb:
    case Up.Clear{}:
      kp.again(am, g, rs, only, hub, hn, Up.hash.of(man1), he, url, tip, tg, root1, nar1, vd, r0, rt0,
        nr0, tip, tag, br, nar1, root1, man1, srcs1, ec, ea, et, Eq.string_eq_self(tip), eco,
        agree_self(Up.hash.of(man1), nar1, root1))
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved to the tip, once its checkout is in
law a.adv:
  for co: Up.Co
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for eco: {Up.checkout(rs, Up.Tree{url, tip, he}) == co : Up.Co}
  {again(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, br), g, rs, only, hub)
    == still(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, br),
      fsays(again(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, br), g, rs,
        only, hub))) : Up.Fate}

def a.adv(co, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et, eco):
  match co:
    case Up.Co{+nar1, +root1, +man1, +srcs1}:
      a.hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man1)}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd,
        am, tip, tag, br, nar1, root1,
        man1, srcs1, ec, ea, et, eco)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: a tip that is another commit, once ancestry is in
law a.onward:
  for asc: Up.Asc
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  {again(Up.dep.onward(asc, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only,
    hub)
    == still(Up.dep.onward(asc, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      fsays(again(Up.dep.onward(asc, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g,
        rs, only, hub))) : Up.Fate}

def a.onward(asc, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et):
  match asc:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          a.adv(Up.checkout(rs, Up.Tree{url, tip, he}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am,
            tip, tag, br, ec, ea, et, {==})
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the pin's own commit, judged by whether its checkout agrees
law a.agree:
  for ag: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r0, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.of(man1), nr0, nar1, rt0, root1) == ag : Bool}
  {again(Up.dep.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0,
    vd}}, tip, "", Up.hash.of(man1)), g, rs, only, hub)
    == still(Up.dep.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0,
      nr0, vd}}, tip, "", Up.hash.of(man1)),
      fsays(again(Up.dep.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg,
        rt0, nr0, vd}}, tip, "", Up.hash.of(man1)), g, rs, only, hub))) : Up.Fate}

def a.agree(
  ag,
  g,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  r0,
  tg,
  rt0,
  nr0,
  vd,
  am,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  ec,
  ea,
  et,
  es,
  eco,
  eag
):
  match ag:
    case True{}:
      kp.again(am, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, r0, rt0, nr0, tip, tag, br,
        nar1, root1, man1, srcs1, ec, ea, et, es, eco, eag)
    case False{}:
      {==}

# LAW: the pin's own commit, once its checkout is in
law a.kept:
  for co: Up.Co
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r0, he}) == co : Up.Co}
  {again(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs, only, hub)
    == still(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag),
      fsays(again(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs,
        only, hub))) : Up.Fate}

def a.kept(co, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et, es, eco):
  match co:
    case Up.Co{+nar1, +root1, +man1, +srcs1}:
      a.agree(U.agree(hh, Up.hash.of(man1), nr0, nar1, rt0, root1), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0,
        nr0, vd, am, tip, tag, br, nar1, root1,
        man1, srcs1, ec, ea, et, es, eco, {==})
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: the tip against the pin
law a.same:
  for s: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == s : Bool}
  {again(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only, hub)
    == still(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      fsays(again(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs,
        only, hub))) : Up.Fate}

def a.same(s, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et, es):
  match s:
    case True{}:
      a.kept(Up.checkout(rs, Up.Tree{url, r0, he}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip,
        tag, br, ec, ea, et, es, {==})
    case False{}:
      a.onward(Up.onward(rs, Up.Above{url, r0, tip}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am,
        tip, tag, br, ec, ea, et)

# LAW: whatever tip the remote named
law a.tip:
  for t: Up.Tip
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == t : Up.Tip}
  {again(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only, hub)
    == still(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}),
      fsays(again(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only,
        hub))) : Up.Fate}

def a.tip(t, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, ec, ea, et):
  match t:
    case Up.At{+tip, +tag, +br}:
      a.same(String.eq(r0, tip), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea,
        et, {==})
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: a pin from a repository that is asked about, whatever it is asked
law a.git:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  {again(Up.dep.one(am, rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only, hub)
    == still(Up.dep.one(am, rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}),
      fsays(again(Up.dep.one(am, rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only,
        hub))) : Up.Fate}

def a.git(am, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, ec, ea):
  match am:
    case U.Hold{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Git{url, r0, tg, rt0, nr0, vd}), re(g, rs), only, hub, M.Dep{hn, hh, he,
        M.Git{url, r0, tg, rt0, nr0, vd}})
        == kept(M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, fsays(Up.dep.one(U.aim(_, M.Git{url, r0, tg, rt0,
          nr0, vd}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Fate}
      nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), U.Hold{}, ea)
      %nea : {Up.dep.one(_, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}})
        == kept(M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, fsays(Up.dep.one(_, re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Fate}
      {==}
    case U.Follow{+ref}:
      a.tip(Up.follow(rs, url, ref), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, U.Follow{ref}, ec, ea,
        {==})
    case U.Forward{}:
      a.tip(Up.forward(rs, url), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, U.Forward{}, ec, ea, {==})

# LAW: a pin from a repository, asked about or not
law a.gsel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, hn) == sel : Bool}
  {again(Up.dep.one(U.aim(sel, M.Git{url, r0, tg, rt0, nr0, vd}), rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg,
    rt0, nr0, vd}}), g, rs, only, hub)
    == still(Up.dep.one(U.aim(sel, M.Git{url, r0, tg, rt0, nr0, vd}), rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0,
      tg, rt0, nr0, vd}}),
      fsays(again(Up.dep.one(U.aim(sel, M.Git{url, r0, tg, rt0, nr0, vd}), rs, only, hub, M.Dep{hn, hh, he, M.Git{url,
        r0, tg, rt0, nr0, vd}}), g, rs, only, hub))) : Up.Fate}

def a.gsel(sel, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, ec):
  match sel:
    case True{}:
      a.git(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd,
        ec, {==})
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), False{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Git{url, r0, tg, rt0, nr0, vd}), re(g, rs), only, hub, M.Dep{hn, hh, he,
        M.Git{url, r0, tg, rt0, nr0, vd}})
        == kept(M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, fsays(Up.dep.one(U.aim(_, M.Git{url, r0, tg, rt0,
          nr0, vd}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Fate}
      {==}

# LAW: a hub pin is held, chosen or not, and held again by the next run
law a.hubsel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for ec: {U.chosen(only, hn) == sel : Bool}
  {again(Up.dep.one(U.aim(sel, M.Hub{}), rs, only, hub, M.Dep{hn, hh, he, M.Hub{}}), g, rs, only, hub)
    == still(Up.dep.one(U.aim(sel, M.Hub{}), rs, only, hub, M.Dep{hn, hh, he, M.Hub{}}),
      fsays(again(Up.dep.one(U.aim(sel, M.Hub{}), rs, only, hub, M.Dep{hn, hh, he, M.Hub{}}), g, rs,
        only, hub))) : Up.Fate}

def a.hubsel(sel, g, rs, only, hub, hn, hh, he, ec):
  match sel:
    case True{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Hub{}), re(g, rs), only, hub, M.Dep{hn, hh, he, M.Hub{}})
        == kept(M.Dep{hn, hh, he, M.Hub{}}, fsays(Up.dep.one(U.aim(_, M.Hub{}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Hub{}}))) : Up.Fate}
      {==}
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), False{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Hub{}), re(g, rs), only, hub, M.Dep{hn, hh, he, M.Hub{}})
        == kept(M.Dep{hn, hh, he, M.Hub{}}, fsays(Up.dep.one(U.aim(_, M.Hub{}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Hub{}}))) : Up.Fate}
      {==}

# LAW: whatever the upgrade makes of a dependency, the next upgrade, against
# the same remote, keeps the pin it left, or stops as it did
law a.one:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +d: M.Dep
  {again(Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), rs, only, hub, d), g, rs,
    only, hub)
    == still(Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), rs, only, hub, d),
      fsays(again(Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), rs, only, hub, d),
        g, rs, only, hub))) : Up.Fate}

def a.one(g, rs, only, hub, d):
  match d:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{}:
          a.hubsel(U.chosen(only, hn), g, rs, only, hub, hn, hh, he, {==})
        case M.Git{+url, +r0, +tg, +rt0, +nr0, +vd}:
          a.gsel(U.chosen(only, hn), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, {==})

# The pin a fate leaves is the one it had whenever the fate says it did not
# move: only `dep.moved` changes a pin, and it says so.

# the pin a fate leaves when it says it did not move, else the one it had
def back(f: Up.Fate, +d: M.Dep) -> M.Dep:
  match f:
    case Up.Became{d2, _o, _n, _p, m, _s, _t}:
      Bool.pick(M.Dep, m, d, d2)
    case Up.Waits{_a}:
      d
    case Up.Halts{_w}:
      d

law moved_back:
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {back(Up.dep.moved(dep, hash, rev, root, nar, manifest, srcs, branch), dep) == dep : M.Dep}

def moved_back(_dep, _hash, _rev, _root, _nar, _manifest, _srcs, _branch):
  {==}

law hub_back:
  for hubbed: Up.Hubbed
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {back(Up.dep.hub(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch), dep) == dep : M.Dep}

def hub_back(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch):
  match hubbed:
    case Up.Clear{}:
      moved_back(dep, hash, rev, root, nar, manifest, srcs, branch)
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

law advance_back:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +rev: String
  for +branch: String
  {back(Up.dep.advance(co, rs, hub, dep, rev, branch), dep) == dep : M.Dep}

def advance_back(co, rs, hub, dep, rev, branch):
  match co:
    case Up.Co{nar, root, +manifest, srcs}:
      hub_back(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(manifest)}), dep, Up.hash.of(manifest),
        rev, root, nar, manifest, srcs, branch)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law verdict_back:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +branch: String
  for +seen: String
  {back(Up.dep.verdict(verdict, rs, hub, dep, tip, branch, seen), dep) == dep : M.Dep}

def verdict_back(verdict, rs, hub, dep, _tip, branch, _seen):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      advance_back(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)), rev, M.dep.entry(dep)}),
        rs, hub, dep, rev, branch)

law kept_back:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  {back(Up.dep.kept(co, rs, hub, dep, tip, tag), dep) == dep : M.Dep}

def kept_back(co, rs, hub, dep, tip, tag):
  match co:
    case Up.Co{nar, root, +manifest, _srcs}:
      verdict_back(U.judge(True{}, True{},
        U.agree(M.dep.hash(dep), Up.hash.of(manifest), M.source.nar(M.source.dep(dep)), nar,
          M.source.root(M.source.dep(dep)), root), tip, tag), rs, hub, dep, tip, "",
        Up.hash.of(manifest))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law onward_back:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {back(Up.dep.onward(asc, rs, hub, dep, tip, tag, branch), dep) == dep : M.Dep}

def onward_back(asc, rs, hub, dep, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      verdict_back(U.judge(False{}, yes, False{}, tip, tag), rs, hub, dep, tip, branch, "")
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law same_back:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {back(Up.dep.same(same, rs, hub, dep, tip, tag, branch), dep) == dep : M.Dep}

def same_back(same, rs, hub, dep, tip, tag, branch):
  match same:
    case True{}:
      kept_back(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), M.dep.entry(dep)}), rs, hub, dep, tip, tag)
    case False{}:
      onward_back(Up.onward(rs, Up.Above{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), tip}), rs, hub, dep, tip, tag, branch)

law tip_back:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  {back(Up.dep.tip(tip, rs, hub, dep), dep) == dep : M.Dep}

def tip_back(tip, rs, hub, dep):
  match tip:
    case Up.At{+rev, tag, branch}:
      same_back(String.eq(M.source.rev(M.source.dep(dep)), rev), rs, hub, dep, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: whatever the upgrade makes of one dependency, what it leaves in the
# ledger has the dependency's name
law one_back:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +dep: M.Dep
  {back(Up.dep.one(aim, rs, only, hub, dep), dep) == dep : M.Dep}

def one_back(aim, rs, _only, hub, dep):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      tip_back(Up.follow(rs, M.source.url(M.source.dep(dep)), ref), rs, hub, dep)
    case U.Forward{}:
      tip_back(Up.forward(rs, M.source.url(M.source.dep(dep))), rs, hub, dep)


# the tool pin a pin leaves when it says it did not move, else the one it had
def tback(p: Up.Pinned, +t: M.Tool) -> M.Tool:
  match p:
    case Up.Pinned{t2, m, _s}:
      Bool.pick(M.Tool, m, t, t2)
    case Up.PinWait{_a}:
      t
    case Up.PinHalt{_w}:
      t

law tpin_tback:
  for short: Bool
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  {tback(Up.tool.pin(short, tool, rev, tag, nar, says), tool) == tool : M.Tool}

def tpin_tback(short, _tool, _rev, _tag, _nar, _says):
  match short:
    case True{}:
      {==}
    case False{}:
      {==}

law weighed_tback:
  for wd: Up.Wd
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {tback(Up.tool.weighed(wd, tool, rev, tag, says), tool) == tool : M.Tool}

def weighed_tback(wd, tool, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      tpin_tback(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_tback:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +ref: String
  {tback(Up.tool.resolved(tip, rs, tool, ref), tool) == tool : M.Tool}

def resolved_tback(tip, rs, tool, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      weighed_tback(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law named_tback:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +url: String
  {tback(Up.tool.named(named, rs, tool, url), tool) == tool : M.Tool}

def named_tback(named, rs, tool, url):
  match named:
    case Up.Named{+ref}:
      resolved_tback(Up.follow(rs, url, ref), rs, tool, ref)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

law tverdict_tback:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +branch: String
  {tback(Up.tool.verdict(verdict, rs, tool, tip, branch), tool) == tool : M.Tool}

def tverdict_tback(verdict, rs, tool, _tip, branch):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      weighed_tback(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, "",
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_nar_tback:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +nar: String
  {tback(Up.tool.kept.nar(fill, rs, tool, tip, tag, nar), tool) == tool : M.Tool}

def tkept_nar_tback(fill, rs, tool, tip, tag, nar):
  match fill:
    case True{}:
      tpin_tback(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tverdict_tback(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")

law tkept_tback:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  {tback(Up.tool.kept(wd, rs, tool, tip, tag), tool) == tool : M.Tool}

def tkept_tback(wd, rs, tool, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      tkept_nar_tback(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law tonward_tback:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +branch: String
  {tback(Up.tool.onward(asc, rs, tool, tip, tag, branch), tool) == tool : M.Tool}

def tonward_tback(asc, rs, tool, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      tverdict_tback(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law tsame_tback:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +branch: String
  {tback(Up.tool.same(same, rs, tool, tip, tag, branch), tool) == tool : M.Tool}

def tsame_tback(same, rs, tool, tip, tag, branch):
  match same:
    case True{}:
      tkept_tback(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), rs, tool, tip, tag)
    case False{}:
      tonward_tback(Up.onward(rs, Up.Above{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool)), tip}), rs, tool, tip, tag, branch)

law ttip_tback:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {tback(Up.tool.tip(tip, rs, tool), tool) == tool : M.Tool}

def ttip_tback(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, branch}:
      tsame_tback(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law taim_tback:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {tback(Up.tool.aim(aim, rs, tool), tool) == tool : M.Tool}

def taim_tback(aim, rs, tool):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      ttip_tback(Up.follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      ttip_tback(Up.forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

law fill_tback:
  for no_rev: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {tback(Up.tool.fill(no_rev, rs, tool), tool) == tool : M.Tool}

def fill_tback(no_rev, rs, tool):
  match no_rev:
    case True{}:
      named_tback(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(tool))), rs,
        M.source.url(M.tool.source(tool)), M.source.tag(M.tool.source(tool))), rs, tool,
        M.source.url(M.tool.source(tool)))
    case False{}:
      taim_tback(U.aim(True{}, M.tool.source(tool)), rs, tool)

law short_tback:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {tback(Up.tool.short(short, rs, tool), tool) == tool : M.Tool}

def short_tback(short, rs, tool):
  match short:
    case True{}:
      fill_tback(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      taim_tback(U.aim(True{}, M.tool.source(tool)), rs, tool)

law git_tback:
  for git: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {tback(Up.tool.git(git, rs, tool), tool) == tool : M.Tool}

def git_tback(git, rs, tool):
  match git:
    case False{}:
      {==}
    case True{}:
      short_tback(Bool.or(String.is_empty(M.source.rev(M.tool.source(tool))),
        String.is_empty(M.source.nar(M.tool.source(tool)))), rs, tool)

# LAW: whatever the upgrade makes of one tool, what it leaves in the ledger has
# the tool's name
law sel_tback:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {tback(Up.tool.sel(sel, rs, tool), tool) == tool : M.Tool}

def sel_tback(sel, rs, tool):
  match sel:
    case False{}:
      {==}
    case True{}:
      git_tback(M.source.is_git(M.tool.source(tool)), rs, tool)


# ---------------------------------------------------------------------------
# one tool, upgraded again

# a tool pin kept as it is, with the lines it says
def pkept(t: M.Tool, s: List<&2, String>) -> Up.Pinned:
  Up.Pinned{t, False{}, s}

# the lines a tool's fate says
def psays(p: Up.Pinned) -> List<&2, String>:
  match p:
    case Up.Pinned{_t, _m, s}:
      s
    case Up.PinWait{_a}:
      []
    case Up.PinHalt{_w}:
      []

# what the next upgrade makes of a tool pin this one left
def again_t.t(+t: M.Tool, +g: String, +rs: List<&2, Up.Reply>, +only: String) -> Up.Pinned:
  Up.tool.sel(U.chosen(only, M.tool.name(t)), re(g, rs), t)

def again_t(p: Up.Pinned, +g: String, +rs: List<&2, Up.Reply>, +only: String) -> Up.Pinned:
  match p:
    case Up.Pinned{+t, _m, _s}:
      again_t.t(t, g, rs, only)
    case Up.PinWait{a}:
      Up.PinWait{a}
    case Up.PinHalt{w}:
      Up.PinHalt{w}

# a tool's fate with the pin it left kept, saying the lines given
def still_t(p: Up.Pinned, s: List<&2, String>) -> Up.Pinned:
  match p:
    case Up.Pinned{t, _m, _s}:
      pkept(t, s)
    case Up.PinWait{a}:
      Up.PinWait{a}
    case Up.PinHalt{w}:
      Up.PinHalt{w}

# LAW: an `or` that answered False answered False on its left
law or_false_l:
  for a: Bool
  for +c: Bool
  for e: {Bool.or(a, c) == False{} : Bool}
  {a == False{} : Bool}

def or_false_l(a, _c, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: and on its right
law or_false_r:
  for a: Bool
  for +c: Bool
  for e: {Bool.or(a, c) == False{} : Bool}
  {c == False{} : Bool}

def or_false_r(a, c, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {c == False{} : Bool}, e)
    case False{}:
      e

# LAW: a pin with a commit is upgraded as a full pin is, however short it is
law short_aim:
  for x: Bool
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for hr: {String.is_empty(r) == False{} : Bool}
  {Up.tool.short(x, rs, M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == Up.tool.aim(U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), rs, M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    : Up.Pinned}

def short_aim(x, rs, n, e, b, url, r, tg, rt, nr, vd, hr):
  match x:
    case False{}:
      {==}
    case True{}:
      nhr = Equal.sym(Bool, String.is_empty(r), False{}, hr)
      %nhr : {Up.tool.fill(_, rs, M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == Up.tool.aim(U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), rs,
          M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}) : Up.Pinned}
      {==}


# LAW: a tool pin at its own tip, weighed there to its own NAR hash, is kept
law tk.same:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for +hn: {String.is_empty(nr) == False{} : Bool}
  for es: {String.eq(r, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r}) == Up.Wd{nw} : Up.Wd}
  for eqn: {String.eq(nr, nw) == True{} : Bool}
  {Up.tool.same(String.eq(r, tip), re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.same(String.eq(r, tip), re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
        tip, tag, br))) : Up.Pinned}

def tk.same(g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, es, ewd, eqn):
  nes = Equal.sym(Bool, String.eq(r, tip), True{}, es)
  %nes : {Up.tool.same(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.same(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)))
    : Up.Pinned}
  ew = Equal.sym(Up.Wd, Up.weighed(re(g, rs), Up.Weigh{url, r}), Up.Wd{nw},
    Equal.trans(Up.Wd, Up.weighed(re(g, rs), Up.Weigh{url, r}), Up.weighed(rs, Up.Weigh{url, r}),
      Up.Wd{nw}, re.weighed(g, rs, url, r), ewd))
  %ew : {Up.tool.kept(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.kept(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)))
    : Up.Pinned}
  nhn = Equal.sym(Bool, String.is_empty(nr), False{}, hn)
  %nhn : {Up.tool.kept.nar(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, nw)
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.kept.nar(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, nw)))
    : Up.Pinned}
  neq = Equal.sym(Bool, String.eq(nr, nw), True{}, eqn)
  %neq : {Up.tool.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs),
      M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, "")
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs),
        M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, ""))) : Up.Pinned}
  {==}

# LAW: the same, once the aim is known
law tk.aim:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for +hn: {String.is_empty(nr) == False{} : Bool}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r}) == Up.Wd{nw} : Up.Wd}
  for eqn: {String.eq(nr, nw) == True{} : Bool}
  {Up.tool.aim(am, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.aim(am, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}

def tk.aim(am, g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, et, es, ewd, eqn):
  match am:
    case U.Hold{}:
      Eq.bit.absurd(&2, {Up.tool.aim(U.Hold{}, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
          psays(Up.tool.aim(U.Hold{}, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})))
        : Up.Pinned}, tip.clash(Up.At{tip, tag, br}, "", et, {==}))
    case U.Follow{+ref}:
      e3 = Equal.sym(Up.Tip, Up.follow(re(g, rs), url, ref), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.follow(re(g, rs), url, ref), Up.follow(rs, url, ref),
          Up.At{tip, tag, br}, re.follow(g, rs, url, ref), et))
      %e3 : {Up.tool.tip(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
          psays(Up.tool.tip(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
      tk.same(g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, es, ewd, eqn)
    case U.Forward{}:
      e3 = Equal.sym(Up.Tip, Up.forward(re(g, rs), url), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.forward(re(g, rs), url), Up.forward(rs, url),
          Up.At{tip, tag, br}, re.forward(g, rs, url), et))
      %e3 : {Up.tool.tip(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
          psays(Up.tool.tip(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
      tk.same(g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, es, ewd, eqn)

# LAW: the next upgrade keeps a tool pin that is at the tip its remote names,
# whose NAR hash is the one the weighing there gave
law tk.again:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr: {String.is_empty(r) == False{} : Bool}
  for +hn: {String.is_empty(nr) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r}) == Up.Wd{nw} : Up.Wd}
  for eqn: {String.eq(nr, nw) == True{} : Bool}
  {again_t.t(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only)
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(again_t.t(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only))) : Up.Pinned}

def tk.again(am, g, rs, only, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, ec, hr, hn, ea, et, es, ewd, eqn):
  nec = Equal.sym(Bool, U.chosen(only, n), True{}, ec)
  %nec : {Up.tool.sel(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.sel(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
  sa = Equal.sym(Up.Pinned,
    Up.tool.short(Bool.or(String.is_empty(r), String.is_empty(nr)), re(g, rs),
      M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}),
    Up.tool.aim(U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), re(g, rs),
      M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}),
    short_aim(Bool.or(String.is_empty(r), String.is_empty(nr)), re(g, rs), n, e, b, url, r, tg, rt,
      nr, vd, hr))
  %sa : {_ == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, psays(_)) : Up.Pinned}
  nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), am, ea)
  %nea : {Up.tool.aim(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == pkept(M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.aim(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
  tk.aim(am, g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, et, es, ewd, eqn)

# LAW: a commit weighed and written into the pin is kept by the next run
law t.pin:
  for gd: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +tagarg: String
  for says: List<&2, String>
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, Bool.pick(String, String.is_empty(tagarg), tg, tagarg), rt0, nr0,
      vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for ewd: {Up.weighed(rs, Up.Weigh{url, tip}) == Up.Wd{nw} : Up.Wd}
  for +egd: {Bool.or(String.is_empty(tip), String.is_empty(nw)) == gd : Bool}
  {again_t(Up.tool.pin(gd, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, nw, says), g, rs, only)
    == still_t(Up.tool.pin(gd, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, nw, says),
      psays(again_t(Up.tool.pin(gd, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, nw, says), g, rs,
        only))) : Up.Pinned}

def t.pin(
  gd,
  g,
  rs,
  only,
  n,
  e,
  b,
  url,
  _r0,
  tg,
  rt0,
  _nr0,
  _vd,
  tagarg,
  _says,
  am,
  tip,
  tag,
  br,
  nw,
  ec,
  ea,
  et,
  ewd,
  egd
):
  match gd:
    case True{}:
      {==}
    case False{}:
      tk.again(am, g, rs, only, n, e, b, url, tip, Bool.pick(String, String.is_empty(tagarg), tg, tagarg),
        M.root.or(rt0), nw, False{}, tip, tag, br, nw, ec,
        or_false_l(String.is_empty(tip), String.is_empty(nw), egd),
        or_false_r(String.is_empty(tip), String.is_empty(nw), egd),
        ea, et, Eq.string_eq_self(tip), ewd, Eq.string_eq_self(nw))

# LAW: a commit, once it is weighed
law t.weighed:
  for wd: Up.Wd
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +tagarg: String
  for says: List<&2, String>
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, Bool.pick(String, String.is_empty(tagarg), tg, tagarg), rt0, nr0,
      vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for ewd: {Up.weighed(rs, Up.Weigh{url, tip}) == wd : Up.Wd}
  {again_t(Up.tool.weighed(wd, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, says), g, rs, only)
    == still_t(Up.tool.weighed(wd, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, says),
      psays(again_t(Up.tool.weighed(wd, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, says), g, rs,
        only))) : Up.Pinned}

def t.weighed(wd, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, tagarg, says, am, tip, tag, br, ec, ea, et, ewd):
  match wd:
    case Up.Wd{+nw}:
      t.pin(Bool.or(String.is_empty(tip), String.is_empty(nw)), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd,
        tagarg, says, am, tip, tag, br, nw,
        ec, ea, et, ewd, {==})
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

# LAW: the pin's own commit, judged by its NAR hash
law t.tagree:
  for ag: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for +hn0: {String.is_empty(nr0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r0}) == Up.Wd{nw} : Up.Wd}
  for eag: {String.eq(nr0, nw) == ag : Bool}
  {again_t(Up.tool.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0,
    vd}}, tip, ""), g, rs, only)
    == still_t(Up.tool.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0,
      vd}}, tip, ""),
      psays(again_t(Up.tool.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0,
        nr0, vd}}, tip, ""), g, rs, only))) : Up.Pinned}

def t.tagree(
  ag,
  g,
  rs,
  only,
  n,
  e,
  b,
  url,
  r0,
  tg,
  rt0,
  nr0,
  vd,
  am,
  tip,
  tag,
  br,
  nw,
  ec,
  hr0,
  hn0,
  ea,
  et,
  es,
  ewd,
  eag
):
  match ag:
    case True{}:
      tk.again(am, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, tip, tag, br, nw, ec, hr0, hn0, ea,
        et, es, ewd, eag)
    case False{}:
      {==}

# LAW: the pin's own commit weighed: filled when it had no NAR hash, else judged
law t.knar:
  for f: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +nw: String
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for +es: {String.eq(r0, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r0}) == Up.Wd{nw} : Up.Wd}
  for ef: {String.is_empty(nr0) == f : Bool}
  {again_t(Up.tool.kept.nar(f, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, nw), g, rs, only)
    == still_t(Up.tool.kept.nar(f, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, nw),
      psays(again_t(Up.tool.kept.nar(f, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, nw), g, rs,
        only))) : Up.Pinned}

def t.knar(f, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, nw, am, tip, tag, br, ec, hr0, ea, et, es, ewd, ef):
  match f:
    case True{}:
      rt = Str.string_eq_true(r0, tip, es)
      ewd2 = Equal.trans(Up.Wd, Up.weighed(rs, Up.Weigh{url, tip}), Up.weighed(rs, Up.Weigh{url, r0}),
        Up.Wd{nw},
        Equal.cong(String, Up.Wd, x => Up.weighed(rs, Up.Weigh{url, x}), tip, r0,
          Equal.sym(String, r0, tip, rt)),
        ewd)
      t.pin(Bool.or(String.is_empty(tip), String.is_empty(nw)), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, "",
        [], am, tip, tag, br, nw, ec,
        ea, et, ewd2, {==})
    case False{}:
      t.tagree(String.eq(nr0, nw), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, nw, ec, hr0, ef,
        ea, et, es, ewd, {==})

# LAW: the pin's own commit, once it is weighed
law t.kept:
  for wd: Up.Wd
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for +es: {String.eq(r0, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r0}) == wd : Up.Wd}
  {again_t(Up.tool.kept(wd, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs, only)
    == still_t(Up.tool.kept(wd, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag),
      psays(again_t(Up.tool.kept(wd, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs,
        only))) : Up.Pinned}

def t.kept(wd, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, hr0, ea, et, es, ewd):
  match wd:
    case Up.Wd{+nw}:
      t.knar(String.is_empty(nr0), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, nw, am, tip, tag, br, ec, hr0, ea,
        et, es, ewd, {==})
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

# LAW: a tip that is another commit, once ancestry is in
law t.onward:
  for asc: Up.Asc
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  {again_t(Up.tool.onward(asc, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only)
    == still_t(Up.tool.onward(asc, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      psays(again_t(Up.tool.onward(asc, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs,
        only))) : Up.Pinned}

def t.onward(asc, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et):
  match asc:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          t.weighed(Up.weighed(rs, Up.Weigh{url, tip}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, "",
            [Up.say.move(n, r0, tip, br)], am, tip,
            tag, br, ec, ea, et, {==})
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the tip against the pin
law t.same:
  for s: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == s : Bool}
  {again_t(Up.tool.same(s, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only)
    == still_t(Up.tool.same(s, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      psays(again_t(Up.tool.same(s, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs,
        only))) : Up.Pinned}

def t.same(s, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, hr0, ea, et, es):
  match s:
    case True{}:
      t.kept(Up.weighed(rs, Up.Weigh{url, r0}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec,
        hr0, ea, et, es, {==})
    case False{}:
      t.onward(Up.onward(rs, Up.Above{url, r0, tip}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag,
        br, ec, ea, et)

# LAW: whatever tip the remote named
law t.tip:
  for t: Up.Tip
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == t : Up.Tip}
  {again_t(Up.tool.tip(t, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.tip(t, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.tip(t, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only))) : Up.Pinned}

def t.tip(t, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, ec, hr0, ea, et):
  match t:
    case Up.At{+tip, +tag, +br}:
      t.same(String.eq(r0, tip), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, hr0, ea, et,
        {==})
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: a pin with a commit, whatever it is asked
law t.aim:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  {again_t(Up.tool.aim(am, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.aim(am, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.aim(am, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only))) : Up.Pinned}

def t.aim(am, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, hr0, ea):
  match am:
    case U.Hold{}:
      nec = Equal.sym(Bool, U.chosen(only, n), True{}, ec)
      %nec : {Up.tool.sel(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}})
        == pkept(M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, psays(Up.tool.sel(_, re(g, rs), M.Tool{n, e, b,
          M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Pinned}
      sa = Equal.sym(Up.Pinned,
        Up.tool.short(Bool.or(String.is_empty(r0), String.is_empty(nr0)), re(g, rs), M.Tool{n, e, b, M.Git{url, r0,
          tg, rt0, nr0, vd}}),
        Up.tool.aim(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), re(g, rs), M.Tool{n, e, b, M.Git{url, r0, tg,
          rt0, nr0, vd}}),
        short_aim(Bool.or(String.is_empty(r0), String.is_empty(nr0)), re(g, rs), n, e, b, url, r0, tg,
          rt0, nr0, vd, hr0))
      %sa : {_ == pkept(M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, psays(_)) : Up.Pinned}
      nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), U.Hold{}, ea)
      %nea : {Up.tool.aim(_, re(g, rs), M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}})
        == pkept(M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, psays(Up.tool.aim(_, re(g, rs), M.Tool{n, e, b,
          M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Pinned}
      {==}
    case U.Follow{+ref}:
      t.tip(Up.follow(rs, url, ref), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, U.Follow{ref}, ec, hr0, ea, {==})
    case U.Forward{}:
      t.tip(Up.forward(rs, url), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, U.Forward{}, ec, hr0, ea, {==})

# whether the ref a pin is pinned from names something
def named.ok(nm: Up.Named) -> Bool:
  match nm:
    case Up.Named{ref}:
      Bool.not(String.is_empty(ref))
    case Up.NamedWait{_a}:
      True{}
    case Up.NamedNo{_w}:
      True{}

# LAW: a branch a remote's HEAD names is a ref, when it names one
law br_ok:
  for name: String
  for +url: String
  {named.ok(Up.heads.branch(name, url)) == True{} : Bool}

def br_ok(name, _url):
  match name:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

law heads_ok:
  for said: Up.Said
  for +url: String
  {named.ok(Up.heads.said(said, url)) == True{} : Bool}

def heads_ok(said, url):
  match said:
    case Up.Said{text}:
      br_ok(Git.tip.branch(Git.rows(String.lines(text))), url)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law best_ok:
  for best: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  {named.ok(Up.tags.best(String.is_empty(best), best, rs, url)) == True{} : Bool}

def best_ok(best, rs, url):
  match best:
    case SNil{}:
      heads_ok(Up.printed(rs, Up.Head{url}, "ls-remote " ++ url), url)
    case SCon{_h, _t}:
      {==}

law tags_ok:
  for said: Up.Said
  for +rs: List<&2, Up.Reply>
  for +url: String
  {named.ok(Up.tags.said(said, rs, url)) == True{} : Bool}

def tags_ok(said, rs, url):
  match said:
    case Up.Said{text}:
      best_ok(Git.choose(Git.tag.names(Git.rows(String.lines(text)))), rs, url)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

# LAW: a pin with no commit is pinned from a ref that names something: its
# tag, or the greatest release tag, or the default branch
law ref_ok:
  for tg: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  {named.ok(Up.tool.ref(String.is_empty(tg), rs, url, tg)) == True{} : Bool}

def ref_ok(tg, rs, url):
  match tg:
    case SNil{}:
      tags_ok(Up.printed(rs, Up.Tags{url}, "ls-remote " ++ url), rs, url)
    case SCon{_h, _t}:
      {==}

# LAW: the pin, with a nonempty ref written in as its tag, is asked about
# that ref
law ea_ref:
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +ref: String
  for +ne: {String.is_empty(ref) == False{} : Bool}
  {U.aim(True{}, M.Git{url, r0, Bool.pick(String, String.is_empty(ref), tg, ref), rt0, nr0, vd})
    == U.Follow{ref} : U.Aim}

def ea_ref(_url, _r0, tg, _rt0, _nr0, _vd, ref, ne):
  nes = Equal.sym(Bool, String.is_empty(ref), False{}, ne)
  %nes : {U.aim.tag(String.is_empty(Bool.pick(String, _, tg, ref)), Bool.pick(String, _, tg, ref))
    == U.Follow{ref} : U.Aim}
  nes2 = Equal.sym(Bool, String.is_empty(ref), False{}, ne)
  %nes2 : {U.aim.tag(_, ref) == U.Follow{ref} : U.Aim}
  {==}

# LAW: a pin with no commit, once its ref resolved
law t.resolved:
  for tp: Up.Tip
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +ref: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for +ne: {String.is_empty(ref) == False{} : Bool}
  for et: {Up.follow(rs, url, ref) == tp : Up.Tip}
  {again_t(Up.tool.resolved(tp, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, ref), g, rs, only)
    == still_t(Up.tool.resolved(tp, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, ref),
      psays(again_t(Up.tool.resolved(tp, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, ref), g, rs,
        only))) : Up.Pinned}

def t.resolved(tp, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ref, ec, ne, et):
  match tp:
    case Up.At{+tip, +tag, +br}:
      t.weighed(Up.weighed(rs, Up.Weigh{url, tip}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ref, [],
        U.Follow{ref}, tip, tag, br, ec,
        ea_ref(url, r0, tg, rt0, nr0, vd, ref, ne), et, {==})
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: a pin with no commit, once its ref is known
law t.named:
  for nm: Up.Named
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for eok: {named.ok(nm) == True{} : Bool}
  {again_t(Up.tool.named(nm, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, url), g, rs, only)
    == still_t(Up.tool.named(nm, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, url),
      psays(again_t(Up.tool.named(nm, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, url), g, rs,
        only))) : Up.Pinned}

def t.named(nm, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, eok):
  match nm:
    case Up.Named{+ref}:
      t.resolved(Up.follow(rs, url, ref), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ref, ec,
        Eq.not.true(String.is_empty(ref), eok), {==})
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

# LAW: a short pin, filled
law t.fill:
  for nf: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for enf: {String.is_empty(r0) == nf : Bool}
  {again_t(Up.tool.fill(nf, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.fill(nf, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.fill(nf, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only))) : Up.Pinned}

def t.fill(nf, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, enf):
  match nf:
    case True{}:
      t.named(Up.tool.ref(String.is_empty(tg), rs, url, tg), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec,
        ref_ok(tg, rs, url))
    case False{}:
      t.aim(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, enf,
        {==})

# LAW: a selected pin from a repository, short or full
law t.short:
  for sh: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for esh: {Bool.or(String.is_empty(r0), String.is_empty(nr0)) == sh : Bool}
  {again_t(Up.tool.short(sh, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.short(sh, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.short(sh, rs, M.Tool{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs,
        only))) : Up.Pinned}

def t.short(sh, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, esh):
  match sh:
    case True{}:
      t.fill(String.is_empty(r0), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, {==})
    case False{}:
      t.aim(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec,
        or_false_l(String.is_empty(r0), String.is_empty(nr0), esh), {==})

# LAW: whatever the upgrade makes of a tool pin, the next upgrade, against the
# same remote, keeps the pin it left, or stops as it did
law t.sel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for s: M.Source
  for ec: {U.chosen(only, n) == sel : Bool}
  {again_t(Up.tool.sel(sel, rs, M.Tool{n, e, b, s}), g, rs, only)
    == still_t(Up.tool.sel(sel, rs, M.Tool{n, e, b, s}),
      psays(again_t(Up.tool.sel(sel, rs, M.Tool{n, e, b, s}), g, rs, only))) : Up.Pinned}

def t.sel(sel, g, rs, only, n, e, b, s, ec):
  match sel:
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, n), False{}, ec)
      %nec : {Up.tool.sel(_, re(g, rs), M.Tool{n, e, b, s})
        == pkept(M.Tool{n, e, b, s}, psays(Up.tool.sel(_, re(g, rs), M.Tool{n, e, b, s}))) : Up.Pinned}
      {==}
    case True{}:
      match s:
        case M.Hub{}:
          {==}
        case M.Git{+url, +r0, +tg, +rt0, +nr0, +vd}:
          t.short(Bool.or(String.is_empty(r0), String.is_empty(nr0)), g, rs, only, n, e, b, url, r0, tg,
            rt0, nr0, vd, ec, {==})

law t.one:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +t: M.Tool
  {again_t(Up.tool.sel(U.chosen(only, M.tool.name(t)), rs, t), g, rs, only)
    == still_t(Up.tool.sel(U.chosen(only, M.tool.name(t)), rs, t),
      psays(again_t(Up.tool.sel(U.chosen(only, M.tool.name(t)), rs, t), g, rs, only))) : Up.Pinned}

def t.one(g, rs, only, t):
  match t:
    case M.Tool{+n, +e, +b, s}:
      t.sel(U.chosen(only, n), g, rs, only, n, e, b, s, {==})

# whether a tool's fate that waits waits on a question
def pwok(p: Up.Pinned) -> Bool:
  match p:
    case Up.Pinned{_t, _m, _s}:
      True{}
    case Up.PinWait{a}:
      Bool.not(List.is_empty(&2, Up.Ask, a))
    case Up.PinHalt{_w}:
      True{}

law tpin_pwok:
  for short: Bool
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  {pwok(Up.tool.pin(short, tool, rev, tag, nar, says)) == True{} : Bool}

def tpin_pwok(short, _tool, _rev, _tag, _nar, _says):
  match short:
    case True{}:
      {==}
    case False{}:
      {==}

law weighed_pwok:
  for wd: Up.Wd
  for +tool: M.Tool
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {pwok(Up.tool.weighed(wd, tool, rev, tag, says)) == True{} : Bool}

def weighed_pwok(wd, tool, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      tpin_pwok(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_pwok:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +ref: String
  {pwok(Up.tool.resolved(tip, rs, tool, ref)) == True{} : Bool}

def resolved_pwok(tip, rs, tool, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      weighed_pwok(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law named_pwok:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +url: String
  {pwok(Up.tool.named(named, rs, tool, url)) == True{} : Bool}

def named_pwok(named, rs, tool, url):
  match named:
    case Up.Named{+ref}:
      resolved_pwok(Up.follow(rs, url, ref), rs, tool, ref)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

law tverdict_pwok:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +branch: String
  {pwok(Up.tool.verdict(verdict, rs, tool, tip, branch)) == True{} : Bool}

def tverdict_pwok(verdict, rs, tool, _tip, branch):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      weighed_pwok(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, "",
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_nar_pwok:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +nar: String
  {pwok(Up.tool.kept.nar(fill, rs, tool, tip, tag, nar)) == True{} : Bool}

def tkept_nar_pwok(fill, rs, tool, tip, tag, nar):
  match fill:
    case True{}:
      tpin_pwok(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tverdict_pwok(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")

law tkept_pwok:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  {pwok(Up.tool.kept(wd, rs, tool, tip, tag)) == True{} : Bool}

def tkept_pwok(wd, rs, tool, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      tkept_nar_pwok(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law tonward_pwok:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +branch: String
  {pwok(Up.tool.onward(asc, rs, tool, tip, tag, branch)) == True{} : Bool}

def tonward_pwok(asc, rs, tool, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      tverdict_pwok(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law tsame_pwok:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  for +tip: String
  for +tag: String
  for +branch: String
  {pwok(Up.tool.same(same, rs, tool, tip, tag, branch)) == True{} : Bool}

def tsame_pwok(same, rs, tool, tip, tag, branch):
  match same:
    case True{}:
      tkept_pwok(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), rs, tool, tip, tag)
    case False{}:
      tonward_pwok(Up.onward(rs, Up.Above{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool)), tip}), rs, tool, tip, tag, branch)

law ttip_pwok:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pwok(Up.tool.tip(tip, rs, tool)) == True{} : Bool}

def ttip_pwok(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, branch}:
      tsame_pwok(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law taim_pwok:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pwok(Up.tool.aim(aim, rs, tool)) == True{} : Bool}

def taim_pwok(aim, rs, tool):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      ttip_pwok(Up.follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      ttip_pwok(Up.forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

law fill_pwok:
  for no_rev: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pwok(Up.tool.fill(no_rev, rs, tool)) == True{} : Bool}

def fill_pwok(no_rev, rs, tool):
  match no_rev:
    case True{}:
      named_pwok(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(tool))), rs,
        M.source.url(M.tool.source(tool)), M.source.tag(M.tool.source(tool))), rs, tool,
        M.source.url(M.tool.source(tool)))
    case False{}:
      taim_pwok(U.aim(True{}, M.tool.source(tool)), rs, tool)

law short_pwok:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pwok(Up.tool.short(short, rs, tool)) == True{} : Bool}

def short_pwok(short, rs, tool):
  match short:
    case True{}:
      fill_pwok(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      taim_pwok(U.aim(True{}, M.tool.source(tool)), rs, tool)

law git_pwok:
  for git: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pwok(Up.tool.git(git, rs, tool)) == True{} : Bool}

def git_pwok(git, rs, tool):
  match git:
    case False{}:
      {==}
    case True{}:
      short_pwok(Bool.or(String.is_empty(M.source.rev(M.tool.source(tool))),
        String.is_empty(M.source.nar(M.tool.source(tool)))), rs, tool)

# LAW: whatever the upgrade makes of one tool, what it leaves in the ledger has
# the tool's name
law sel_pwok:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Tool
  {pwok(Up.tool.sel(sel, rs, tool)) == True{} : Bool}

def sel_pwok(sel, rs, tool):
  match sel:
    case False{}:
      {==}
    case True{}:
      git_pwok(M.source.is_git(M.tool.source(tool)), rs, tool)


# ---------------------------------------------------------------------------
# the walks, upgraded again

# the dependencies a walk leaves
def dd.ds(dd: Up.Deps) -> List<&2, M.Dep>:
  Up.Deps{ds, _ss, _es, _m, _sy, _tr, _asks, _bad} = dd
  ds

# the lines a walk says
def dd.says(dd: Up.Deps) -> List<&2, String>:
  Up.Deps{_ds, _ss, _es, _m, sy, _tr, _asks, _bad} = dd
  sy

# a walk that keeps every dependency and asks nothing
def dsettle(ds: List<&2, M.Dep>, s: List<&2, String>) -> Up.Deps:
  Up.Deps{ds, [], [], False{}, s, [], [], ""}

# whether a walk refuses or still asks
def dunc(dd: Up.Deps) -> Bool:
  Up.Deps{_ds, _ss, _es, _m, _sy, _tr, asks, bad} = dd
  Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks)))

# the dependencies a walk leaves when it neither refuses, asks, nor moves a
# pin, else the ones it was given
def dstay(dd: Up.Deps, +ds: List<&2, M.Dep>) -> List<&2, M.Dep>:
  Up.Deps{dds, _ss, _es, dm, _sy, _tr, asks, bad} = dd
  Bool.pick(List<&2, M.Dep>,
    Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))), dm),
    ds, dds)

# LAW: one step of the walk: the next run keeps the pin this one left in front
law w.step:
  for f: Up.Fate
  for r: Up.Deps
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for ha: {again(f, g, rs, only, hub) == still(f, fsays(again(f, g, rs, only, hub))) : Up.Fate}
  for ih: {Up.deps.walk(re(g, rs), only, hub, dd.ds(r))
    == dsettle(dd.ds(r), dd.says(Up.deps.walk(re(g, rs), only, hub, dd.ds(r)))) : Up.Deps}
  {Up.deps.walk(re(g, rs), only, hub, dd.ds(Up.deps.join(f, r)))
    == dsettle(dd.ds(Up.deps.join(f, r)), dd.says(Up.deps.walk(re(g, rs), only, hub,
      dd.ds(Up.deps.join(f, r))))) : Up.Deps}

def w.step(f, r, g, rs, only, hub, ha, ih):
  match f:
    case Up.Became{+d, o, n, p, m, s, t}:
      match r:
        case Up.Deps{+ds, ss, es, any, sy, tr, asks, bad}:
          nha = Equal.sym(Up.Fate, again.d(d, g, rs, only, hub),
            kept(d, fsays(again.d(d, g, rs, only, hub))), ha)
          %nha : {Up.deps.join(_, Up.deps.walk(re(g, rs), only, hub, ds))
            == dsettle(d <> ds, dd.says(Up.deps.join(_, Up.deps.walk(re(g, rs), only, hub, ds))))
            : Up.Deps}
          nih = Equal.sym(Up.Deps, Up.deps.walk(re(g, rs), only, hub, ds),
            dsettle(ds, dd.says(Up.deps.walk(re(g, rs), only, hub, ds))), ih)
          %nih : {Up.deps.join(kept(d, fsays(again.d(d, g, rs, only, hub))), _)
            == dsettle(d <> ds, dd.says(Up.deps.join(kept(d, fsays(again.d(d, g, rs, only, hub))), _)))
            : Up.Deps}
          {==}
    case Up.Waits{+a}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          ih
    case Up.Halts{+w}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          ih

# LAW: the next upgrade, against the same remote, walks the dependencies this
# one left and keeps every one: it moves nothing, removes nothing, stops
# naming no hash, checks nothing out, asks nothing and refuses nothing
law w.all:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {Up.deps.walk(re(g, rs), only, hub, dd.ds(Up.deps.walk(rs, only, hub, ds)))
    == dsettle(dd.ds(Up.deps.walk(rs, only, hub, ds)), dd.says(Up.deps.walk(re(g, rs), only, hub,
      dd.ds(Up.deps.walk(rs, only, hub, ds))))) : Up.Deps}

def w.all(g, rs, only, hub, ds):
  match ds:
    case []:
      {==}
    case +h <> +t:
      w.step(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, t), g, rs, only, hub, a.one(g, rs, only, hub, h), w.all(g, rs, only, hub, t))

# LAW: an `or` with a left half that answered True answers the same whatever
# its right half is
law or_left_same:
  for u: Bool
  for +a: Bool
  for +b: Bool
  for e: {u == True{} : Bool}
  {Bool.or(u, a) == Bool.or(u, b) : Bool}

def or_left_same(u, a, b, e):
  ne = Equal.sym(Bool, u, True{}, e)
  %ne : {Bool.or(_, a) == Bool.or(_, b) : Bool}
  {==}

# LAW: a scan of names whose rest answers the same answers the same
law known.step_cong:
  for c: Bool
  for +u: Bool
  for +k1: Bool
  for +k2: Bool
  for ih: {Bool.or(u, k1) == Bool.or(u, k2) : Bool}
  {Bool.or(u, U.known.step(c, _x => k1)) == Bool.or(u, U.known.step(c, _y => k2)) : Bool}

def known.step_cong(c, _u, _k1, _k2, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: a walk that waits with a question refuses or asks
law waits_unc:
  for a: List<&2, Up.Ask>
  for +bad: String
  for +asks: List<&2, Up.Ask>
  for e: {Bool.not(List.is_empty(&2, Up.Ask, a)) == True{} : Bool}
  {Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks))))
    == True{} : Bool}

def waits_unc(a, bad, asks, e):
  match a:
    case []:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, [], asks)))) == True{} : Bool}, e)
    case x <> xs:
      mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})

# LAW: one step of the walk keeps the names the ledger can be asked about,
# unless the walk refuses or asks
law kd.step:
  for f: Up.Fate
  for r: Up.Deps
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +x: String
  for fine: {mv.fine(f, M.dep.name(h)) == (M.dep.name(h), True{}) : String & Bool}
  for ih: {Bool.or(dunc(r), U.known.in(dd.ds(r), x)) == Bool.or(dunc(r), U.known.in(t, x)) : Bool}
  {Bool.or(dunc(Up.deps.join(f, r)), U.known.in(dd.ds(Up.deps.join(f, r)), x))
    == Bool.or(dunc(Up.deps.join(f, r)), U.known.in(h <> t, x)) : Bool}

def kd.step(f, r, h, t, x, fine, ih):
  match f:
    case Up.Became{d, o, n, p, m, s, tr}:
      match r:
        case Up.Deps{+ds, ss, es, any, sy, trr, +asks, +bad}:
          en = Equal.cong(String & Bool, String, q => mv.fst(q), (M.dep.name(d), True{}),
            (M.dep.name(h), True{}), fine)
          nen = Equal.sym(String, M.dep.name(d), M.dep.name(h), en)
          %nen : {Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              U.known.step(String.eq(_, x), _u => U.known.in(ds, x)))
            == Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              U.known.step(String.eq(M.dep.name(h), x), _v => U.known.in(t, x))) : Bool}
          known.step_cong(String.eq(M.dep.name(h), x),
            Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
            U.known.in(ds, x), U.known.in(t, x), ih)
    case Up.Waits{+a}:
      match r:
        case Up.Deps{+ds, ss, es, +any, sy, trr, +asks, +bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))),
            U.known.in(ds, x), U.known.in(h <> t, x),
            waits_unc(a, bad, asks, Equal.cong(String & Bool, Bool, q => mv.snd(q),
              (M.dep.name(h), Bool.not(List.is_empty(&2, Up.Ask, a))), (M.dep.name(h), True{}), fine)))
    case Up.Halts{+w}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, trr, +asks, bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))),
            U.known.in(ds, x), U.known.in(h <> t, x),
            mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
              mv.halt_not(w)))

# LAW: a walk that neither refuses nor asks keeps every name the ledger can
# be asked about
law kd.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +x: String
  {Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.in(dd.ds(Up.deps.walk(rs, only, hub, ds)), x))
    == Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.in(ds, x)) : Bool}

def kd.all(rs, only, hub, ds, x):
  match ds:
    case []:
      {==}
    case +h <> +t:
      kd.step(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, t), h, t, x,
        mv.fine_one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        kd.all(rs, only, hub, t, x))

# LAW: and so the dependency `--package` names, when there is one
law kd.known.go:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.go(b, dd.ds(Up.deps.walk(rs, only, hub, ds)), only))
    == Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.go(b, ds, only)) : Bool}

def kd.known.go(b, rs, only, hub, ds):
  match b:
    case True{}:
      {==}
    case False{}:
      kd.all(rs, only, hub, ds, only)

law kd.known:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known(only, dd.ds(Up.deps.walk(rs, only, hub, ds))))
    == Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known(only, ds)) : Bool}

def kd.known(rs, only, hub, ds):
  kd.known.go(String.is_empty(only), rs, only, hub, ds)

# LAW: a list kept in front of a list kept
law pick_cons:
  for c: Bool
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for hd: {d == h : M.Dep}
  for ih: {Bool.pick(List<&2, M.Dep>, c, t, ds) == t : List<&2, M.Dep>}
  {Bool.pick(List<&2, M.Dep>, c, h <> t, d <> ds) == h <> t : List<&2, M.Dep>}

def pick_cons(c, h, t, d, ds, hd, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.trans(List<&2, M.Dep>, d <> ds, h <> ds, h <> t,
        Equal.cong(M.Dep, List<&2, M.Dep>, y => y <> ds, d, h, hd),
        Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>, y => h <> y, ds, t, ih))

# LAW: a pick whose condition answered True is its first
law pick_true:
  for c: Bool
  for +a: List<&2, M.Dep>
  for +b: List<&2, M.Dep>
  for e: {c == True{} : Bool}
  {Bool.pick(List<&2, M.Dep>, c, a, b) == a : List<&2, M.Dep>}

def pick_true(c, a, b, e):
  ne = Equal.sym(Bool, c, True{}, e)
  %ne : {Bool.pick(List<&2, M.Dep>, _, a, b) == a : List<&2, M.Dep>}
  {==}

# LAW: a pin in front, whether it moved or not
law dq.moved:
  for m: Bool
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for +any: Bool
  for +asks: List<&2, Up.Ask>
  for +bad: String
  for hb: {Bool.pick(M.Dep, m, h, d) == h : M.Dep}
  for ih: {Bool.pick(List<&2, M.Dep>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), any), t, ds) == t : List<&2, M.Dep>}
  {Bool.pick(List<&2, M.Dep>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), Bool.or(m, any)), h <> t, d <> ds) == h <> t
    : List<&2, M.Dep>}

def dq.moved(m, h, t, d, ds, any, asks, bad, hb, ih):
  match m:
    case True{}:
      pick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), True{}), h <> t, d <> ds,
        mv.or_r(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
          True{}, {==}))
    case False{}:
      pick_cons(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h, t, d, ds, hb, ih)

# LAW: one step of the walk: a pin that says it did not move is the one it was
law dq.step:
  for f: Up.Fate
  for r: Up.Deps
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for hb: {back(f, h) == h : M.Dep}
  for fine: {mv.fine(f, M.dep.name(h)) == (M.dep.name(h), True{}) : String & Bool}
  for ih: {dstay(r, t) == t : List<&2, M.Dep>}
  {dstay(Up.deps.join(f, r), h <> t) == h <> t : List<&2, M.Dep>}

def dq.step(f, r, h, t, hb, fine, ih):
  match f:
    case Up.Became{+d, o, n, p, m, s, tr}:
      match r:
        case Up.Deps{+ds, ss, es, +any, sy, trr, +asks, +bad}:
          dq.moved(m, h, t, d, ds, any, asks, bad, hb, ih)
    case Up.Waits{+a}:
      match r:
        case Up.Deps{+ds, ss, es, +any, sy, trr, +asks, +bad}:
          pick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(bad)),
                Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any,
              waits_unc(a, bad, asks, Equal.cong(String & Bool, Bool, q => mv.snd(q),
                (M.dep.name(h), Bool.not(List.is_empty(&2, Up.Ask, a))), (M.dep.name(h), True{}), fine))))
    case Up.Halts{+w}:
      match r:
        case Up.Deps{ds, ss, es, +any, sy, trr, +asks, bad}:
          pick_true(Bool.or(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
                Bool.not(List.is_empty(&2, Up.Ask, asks))), any,
              mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
                mv.halt_not(w))))

# LAW: a walk that neither refuses, asks, nor moves a pin leaves the
# dependencies it was given
law dq.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {dstay(Up.deps.walk(rs, only, hub, ds), ds) == ds : List<&2, M.Dep>}

def dq.all(rs, only, hub, ds):
  match ds:
    case []:
      {==}
    case +h <> +t:
      dq.step(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, t), h, t,
        one_back(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        mv.fine_one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        dq.all(rs, only, hub, t))

# the tool pins a walk leaves
def tt.ts(tt: Up.Tools) -> List<&2, M.Tool>:
  Up.Tools{ts, _m, _sy, _asks, _bad} = tt
  ts

# the lines a walk over tools says
def tt.says(tt: Up.Tools) -> List<&2, String>:
  Up.Tools{_ts, _m, sy, _asks, _bad} = tt
  sy

# a walk that keeps every tool pin and asks nothing
def tsettle(ts: List<&2, M.Tool>, s: List<&2, String>) -> Up.Tools:
  Up.Tools{ts, False{}, s, [], ""}

# whether a walk over tools refuses or still asks
def tunc(tt: Up.Tools) -> Bool:
  Up.Tools{_ts, _m, _sy, asks, bad} = tt
  Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks)))

# the tool pins a walk leaves when it neither refuses, asks, nor moves a pin,
# else the ones it was given
def tstay(tt: Up.Tools, +ts: List<&2, M.Tool>) -> List<&2, M.Tool>:
  Up.Tools{tts, tm, _sy, asks, bad} = tt
  Bool.pick(List<&2, M.Tool>,
    Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))), tm),
    ts, tts)

# LAW: one step of the walk over tools
law tw.step:
  for p: Up.Pinned
  for r: Up.Tools
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for ha: {again_t(p, g, rs, only) == still_t(p, psays(again_t(p, g, rs, only))) : Up.Pinned}
  for ih: {Up.tools.walk(re(g, rs), only, tt.ts(r))
    == tsettle(tt.ts(r), tt.says(Up.tools.walk(re(g, rs), only, tt.ts(r)))) : Up.Tools}
  {Up.tools.walk(re(g, rs), only, tt.ts(Up.tools.join(p, r)))
    == tsettle(tt.ts(Up.tools.join(p, r)), tt.says(Up.tools.walk(re(g, rs), only,
      tt.ts(Up.tools.join(p, r))))) : Up.Tools}

def tw.step(p, r, g, rs, only, ha, ih):
  match p:
    case Up.Pinned{+t, m, s}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          nha = Equal.sym(Up.Pinned, again_t.t(t, g, rs, only),
            pkept(t, psays(again_t.t(t, g, rs, only))), ha)
          %nha : {Up.tools.join(_, Up.tools.walk(re(g, rs), only, ts))
            == tsettle(t <> ts, tt.says(Up.tools.join(_, Up.tools.walk(re(g, rs), only, ts))))
            : Up.Tools}
          nih = Equal.sym(Up.Tools, Up.tools.walk(re(g, rs), only, ts),
            tsettle(ts, tt.says(Up.tools.walk(re(g, rs), only, ts))), ih)
          %nih : {Up.tools.join(pkept(t, psays(again_t.t(t, g, rs, only))), _)
            == tsettle(t <> ts, tt.says(Up.tools.join(pkept(t, psays(again_t.t(t, g, rs, only))), _)))
            : Up.Tools}
          {==}
    case Up.PinWait{+a}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          ih
    case Up.PinHalt{+w}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          ih

# LAW: the next upgrade, against the same remote, keeps every tool pin this
# one left
law tw.all:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Tool>
  {Up.tools.walk(re(g, rs), only, tt.ts(Up.tools.walk(rs, only, ts)))
    == tsettle(tt.ts(Up.tools.walk(rs, only, ts)), tt.says(Up.tools.walk(re(g, rs), only,
      tt.ts(Up.tools.walk(rs, only, ts))))) : Up.Tools}

def tw.all(g, rs, only, ts):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tw.step(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, t), g, rs, only,
        t.one(g, rs, only, h), tw.all(g, rs, only, t))

# LAW: a scan of tool names whose rest answers the same answers the same
law tool.step_cong:
  for c: Bool
  for +u: Bool
  for +k1: Bool
  for +k2: Bool
  for ih: {Bool.or(u, k1) == Bool.or(u, k2) : Bool}
  {Bool.or(u, M.tool.step(c, _x => k1)) == Bool.or(u, M.tool.step(c, _y => k2)) : Bool}

def tool.step_cong(c, _u, _k1, _k2, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: one step of the walk over tools keeps the names `--package` can ask
# about, unless the walk refuses or asks
law tkd.step:
  for p: Up.Pinned
  for r: Up.Tools
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for +x: String
  for nm: {pinned.name(p, M.tool.name(h)) == M.tool.name(h) : String}
  for ok: {pwok(p) == True{} : Bool}
  for ih: {Bool.or(tunc(r), M.tool.has(tt.ts(r), x)) == Bool.or(tunc(r), M.tool.has(t, x)) : Bool}
  {Bool.or(tunc(Up.tools.join(p, r)), M.tool.has(tt.ts(Up.tools.join(p, r)), x))
    == Bool.or(tunc(Up.tools.join(p, r)), M.tool.has(h <> t, x)) : Bool}

def tkd.step(p, r, h, t, x, nm, ok, ih):
  match p:
    case Up.Pinned{pt, m, s}:
      match r:
        case Up.Tools{+ts, any, sy, +asks, +bad}:
          nen = Equal.sym(String, M.tool.name(pt), M.tool.name(h), nm)
          %nen : {Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              M.tool.step(String.eq(_, x), _u => M.tool.has(ts, x)))
            == Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              M.tool.step(String.eq(M.tool.name(h), x), _v => M.tool.has(t, x))) : Bool}
          tool.step_cong(String.eq(M.tool.name(h), x),
            Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
            M.tool.has(ts, x), M.tool.has(t, x), ih)
    case Up.PinWait{+a}:
      match r:
        case Up.Tools{+ts, any, sy, +asks, +bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))),
            M.tool.has(ts, x), M.tool.has(h <> t, x), waits_unc(a, bad, asks, ok))
    case Up.PinHalt{+w}:
      match r:
        case Up.Tools{+ts, any, sy, +asks, bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))),
            M.tool.has(ts, x), M.tool.has(h <> t, x),
            mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
              mv.halt_not(w)))

law tkd.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Tool>
  for +x: String
  {Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.has(tt.ts(Up.tools.walk(rs, only, ts)), x))
    == Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.has(ts, x)) : Bool}

def tkd.all(rs, only, ts, x):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tkd.step(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, t), h, t, x,
        sel_name(U.chosen(only, M.tool.name(h)), rs, h), sel_pwok(U.chosen(only, M.tool.name(h)), rs, h),
        tkd.all(rs, only, t, x))

law tkd.known.go:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Tool>
  {Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known.go(b, tt.ts(Up.tools.walk(rs, only, ts)), only))
    == Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known.go(b, ts, only)) : Bool}

def tkd.known.go(b, rs, only, ts):
  match b:
    case True{}:
      {==}
    case False{}:
      tkd.all(rs, only, ts, only)

law tkd.known:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Tool>
  {Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known(only, tt.ts(Up.tools.walk(rs, only, ts))))
    == Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known(only, ts)) : Bool}

def tkd.known(rs, only, ts):
  tkd.known.go(String.is_empty(only), rs, only, ts)

# LAW: a list of tool pins kept in front of a list kept
law tpick_cons:
  for c: Bool
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for +d: M.Tool
  for +ds: List<&2, M.Tool>
  for hd: {d == h : M.Tool}
  for ih: {Bool.pick(List<&2, M.Tool>, c, t, ds) == t : List<&2, M.Tool>}
  {Bool.pick(List<&2, M.Tool>, c, h <> t, d <> ds) == h <> t : List<&2, M.Tool>}

def tpick_cons(c, h, t, d, ds, hd, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.trans(List<&2, M.Tool>, d <> ds, h <> ds, h <> t,
        Equal.cong(M.Tool, List<&2, M.Tool>, y => y <> ds, d, h, hd),
        Equal.cong(List<&2, M.Tool>, List<&2, M.Tool>, y => h <> y, ds, t, ih))

law tpick_true:
  for c: Bool
  for +a: List<&2, M.Tool>
  for +b: List<&2, M.Tool>
  for e: {c == True{} : Bool}
  {Bool.pick(List<&2, M.Tool>, c, a, b) == a : List<&2, M.Tool>}

def tpick_true(c, a, b, e):
  ne = Equal.sym(Bool, c, True{}, e)
  %ne : {Bool.pick(List<&2, M.Tool>, _, a, b) == a : List<&2, M.Tool>}
  {==}

law tq.moved:
  for m: Bool
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for +d: M.Tool
  for +ds: List<&2, M.Tool>
  for +any: Bool
  for +asks: List<&2, Up.Ask>
  for +bad: String
  for hb: {Bool.pick(M.Tool, m, h, d) == h : M.Tool}
  for ih: {Bool.pick(List<&2, M.Tool>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), any), t, ds) == t : List<&2, M.Tool>}
  {Bool.pick(List<&2, M.Tool>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), Bool.or(m, any)), h <> t, d <> ds) == h <> t
    : List<&2, M.Tool>}

def tq.moved(m, h, t, d, ds, any, asks, bad, hb, ih):
  match m:
    case True{}:
      tpick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), True{}), h <> t, d <> ds,
        mv.or_r(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
          True{}, {==}))
    case False{}:
      tpick_cons(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h, t, d, ds, hb, ih)

law tq.step:
  for p: Up.Pinned
  for r: Up.Tools
  for +h: M.Tool
  for +t: List<&2, M.Tool>
  for hb: {tback(p, h) == h : M.Tool}
  for ok: {pwok(p) == True{} : Bool}
  for ih: {tstay(r, t) == t : List<&2, M.Tool>}
  {tstay(Up.tools.join(p, r), h <> t) == h <> t : List<&2, M.Tool>}

def tq.step(p, r, h, t, hb, ok, ih):
  match p:
    case Up.Pinned{+d, m, s}:
      match r:
        case Up.Tools{+ds, +any, sy, +asks, +bad}:
          tq.moved(m, h, t, d, ds, any, asks, bad, hb, ih)
    case Up.PinWait{+a}:
      match r:
        case Up.Tools{+ds, +any, sy, +asks, +bad}:
          tpick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(bad)),
                Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any,
              waits_unc(a, bad, asks, ok)))
    case Up.PinHalt{+w}:
      match r:
        case Up.Tools{+ds, +any, sy, +asks, bad}:
          tpick_true(Bool.or(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
                Bool.not(List.is_empty(&2, Up.Ask, asks))), any,
              mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
                mv.halt_not(w))))

law tq.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Tool>
  {tstay(Up.tools.walk(rs, only, ts), ts) == ts : List<&2, M.Tool>}

def tq.all(rs, only, ts):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tq.step(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, t), h, t,
        sel_tback(U.chosen(only, M.tool.name(h)), rs, h), sel_pwok(U.chosen(only, M.tool.name(h)), rs, h),
        tq.all(rs, only, t))

# ---------------------------------------------------------------------------
# the upgrade, upgraded again

# what an upgrade decided, less the lines it says
def view(nx: Up.Next) -> Up.Next:
  Up.Next{mo, rd, st, ak, tr, vs, _sy, ed, fd, dr, sw} = nx
  Up.Next{mo, rd, st, ak, tr, vs, [], ed, fd, dr, sw}

# the hashes a ledger model vendors
def vends.of(model: M.Read) -> List<&2, String>:
  match model:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, ds, _ts} = m
      I.vended(ds)

# the `.gitignore` an upgrade of a ledger model writes, given the one it reads
def gi.of(model: M.Read, +g: String) -> List<&2, Up.Edit>:
  match model:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, +ds, _ts} = m
      +allow = I.sync(ds, g)
      Up.edit.if(String.eq(allow, g), ".gitignore", allow, [])

# what an upgrade of a ledger model decides when every pin is at its tip:
# the model as it is, nothing refused, asked, checked out, moved or removed,
# and at most `.gitignore` written
def target(+model: M.Read, +g: String) -> Up.Next:
  Up.Next{model, model, "", [], [], vends.of(model), [], gi.of(model, g), [], [], []}

# the second upgrade's decision, and the ledger the first one's lock was made
# from
def core.lhs(+nx: Up.Next, +only: String, +g: String, +rs: List<&2, Up.Reply>) -> Up.Next & M.Read:
  (view(Up.next(only, Up.next.model(nx), re(g, rs))), Up.next.read(nx))

# what they are: the target, and the ledger the first one wrote, read
def core.rhs(+nx: Up.Next, +g: String, ledger: Maybe<&2, String>) -> Up.Next & M.Read:
  (target(Up.next.model(nx), g), W.parsed(Laws.ledger.left(Up.next.edits(nx), ledger)))

# LAW: a pair of equals
law pair_eq:
  for a1: Up.Next
  for a2: Up.Next
  for b1: M.Read
  for b2: M.Read
  for e1: {a1 == a2 : Up.Next}
  for e2: {b1 == b2 : M.Read}
  {(a1, b1) == (a2, b2) : Up.Next & M.Read}

def pair_eq(a1, a2, b1, b2, e1, e2):
  Equal.trans(Up.Next & M.Read, (a1, b1), (a2, b1), (a2, b2),
    Equal.cong(Up.Next, Up.Next & M.Read, x => (x, b1), a1, a2, e1),
    Equal.cong(M.Read, Up.Next & M.Read, y => (a2, y), b1, b2, e2))

# LAW: an upgrade that writes at most `.gitignore` leaves ez.toml as it was
law li:
  for b: Bool
  for +allow: String
  for +ledger: Maybe<&2, String>
  {Laws.ledger.left(Up.edit.if(b, ".gitignore", allow, []), ledger) == ledger : Maybe<&2, String>}

def li(b, _allow, _ledger):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}


# LAW: an upgrade of a ledger whose every pin is at its tip, against the same
# remote, decides the target: the ledger as it is, and nothing moved
law c.second:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Tool>
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for kn: {Bool.or(U.known(only, dds), M.tool.known(only, tts)) == True{} : Bool}
  {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, re(g,
    rs))) == target(M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, g) : Up.Next}

def c.second(g, rs, only, name, entry, bin, hub, dds, tts, hw, tw, kn):
  nkn = Equal.sym(Bool, Bool.or(U.known(only, dds), M.tool.known(only, tts)), True{}, kn)
  %nkn : {view(Up.known(_, only, re(g, rs), M.Manifest{name, entry, bin, hub, dds,
    tts})) == target(M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, g) : Up.Next}
  nhw = Equal.sym(Up.Deps, Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds), dsettle(dds, dd.says(Up.deps.walk(re(g,
    rs), only, M.hub.or(hub), dds))), hw)
  %nhw : {view(Up.pins(_, Up.tools.walk(re(g, rs), only, tts), re(g, rs), M.Manifest{name, entry, bin, hub, dds,
    tts})) == target(M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, g) : Up.Next}
  ntw = Equal.sym(Up.Tools, Up.tools.walk(re(g, rs), only, tts), tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only,
    tts))), tw)
  %ntw : {view(Up.pins(dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds))), _, re(g, rs),
    M.Manifest{name, entry, bin, hub, dds, tts}))
    == target(M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, g) : Up.Next}
  {==}

# LAW: and one that moved nothing is one whose pins are the ones it walked
law c.same:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Tool>
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for kn: {Bool.or(U.known(only, dds), M.tool.known(only, tts)) == True{} : Bool}
  for hq: {dds == ds : List<&2, M.Dep>}
  for tq: {tts == ts : List<&2, M.Tool>}
  {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, ds, ts}}, re(g, rs))) == target(M.Good{M.Manifest{name,
    entry, bin, hub, ds, ts}}, g) : Up.Next}

def c.same(g, rs, only, name, entry, bin, hub, _ds, ts, dds, tts, hw, tw, kn, hq, tq):
  %hq : {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, _, ts}}, re(g, rs)))
    == target(M.Good{M.Manifest{name, entry, bin, hub, _, ts}}, g) : Up.Next}
  %tq : {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, dds, _}}, re(g, rs)))
    == target(M.Good{M.Manifest{name, entry, bin, hub, dds, _}}, g) : Up.Next}
  c.second(g, rs, only, name, entry, bin, hub, dds, tts, hw, tw, kn)


# LAW: the known names, walked
law c.kn:
  for +only: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Tool>
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  {Bool.or(U.known(only, dds), M.tool.known(only, tts)) == True{} : Bool}

def c.kn(only, ds, ts, dds, tts, ek, hk, tk):
  Equal.trans(Bool, Bool.or(U.known(only, dds), M.tool.known(only, tts)),
    Bool.or(U.known(only, ds), M.tool.known(only, tts)), True{},
    Equal.cong(Bool, Bool, x => Bool.or(x, M.tool.known(only, tts)), U.known(only, dds), U.known(only, ds), hk),
    Equal.trans(Bool, Bool.or(U.known(only, ds), M.tool.known(only, tts)),
      Bool.or(U.known(only, ds), M.tool.known(only, ts)), True{},
      Equal.cong(Bool, Bool, y => Bool.or(U.known(only, ds), y), M.tool.known(only, tts),
        M.tool.known(only, ts), tk),
      ek))

# LAW: every answer in; whether a pin moved decides the ledger the first run
# wrote and the second reads
law c.done:
  for dm: Bool
  for tm: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for +ig: String
  for +fs: List<&2, Up.Found>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  for tq: {Bool.pick(List<&2, M.Tool>, tm, ts, tts) == ts : List<&2, M.Tool>}
  {core.lhs(Up.done(M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""},
    Up.Tools{tts, tm, tsy, [], ""}, ig, fs), only, g, rs) == core.rhs(Up.done(M.Manifest{name, entry, bin, hub, ds,
      ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig, fs), g,
        ledger) : Up.Next & M.Read}

def c.done(
  dm,
  tm,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  _ss,
  _es,
  _dsy,
  _dtr,
  tts,
  _tsy,
  ig,
  _fs,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq
):
  match dm:
    case True{}:
      Equal.cong(Up.Next, Up.Next & M.Read, x => (x, M.parse(Rend.show(M.Manifest{name, entry, bin, hub, dds, tts}))),
        view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, re(g, rs))),
          target(M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, g),
        c.second(g, rs, only, name, entry, bin, hub, dds, tts, hw, tw, c.kn(only, ds, ts, dds, tts, ek, hk, tk)))
    case False{}:
      match tm:
        case True{}:
          Equal.cong(Up.Next, Up.Next & M.Read, x => (x, M.parse(Rend.show(M.Manifest{name, entry, bin, hub, dds,
            tts}))),
            view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, re(g, rs))),
              target(M.Good{M.Manifest{name, entry, bin, hub, dds, tts}}, g),
            c.second(g, rs, only, name, entry, bin, hub, dds, tts, hw, tw,
              c.kn(only, ds, ts, dds, tts, ek, hk, tk)))
        case False{}:
          pair_eq(view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, ds, ts}}, re(g, rs))),
            target(M.Good{M.Manifest{name, entry, bin, hub, ds, ts}}, g),
            M.Good{M.Manifest{name, entry, bin, hub, ds, ts}},
            W.parsed(Laws.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []),
              ledger)),
            c.same(g, rs, only, name, entry, bin, hub, ds, ts, dds, tts, hw, tw,
              c.kn(only, ds, ts, dds, tts, ek, hk, tk), hq, tq),
            Equal.sym(M.Read,
              W.parsed(Laws.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []),
                ledger)),
              M.Good{M.Manifest{name, entry, bin, hub, ds, ts}},
              Equal.trans(M.Read,
                W.parsed(Laws.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore",
                  I.sync(dds, ig), []), ledger)),
                W.parsed(ledger), M.Good{M.Manifest{name, entry, bin, hub, ds, ts}},
                Equal.cong(Maybe<&2, String>, M.Read, x => W.parsed(x),
                  Laws.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []),
                    ledger), ledger, li(String.eq(I.sync(dds, ig), ig), I.sync(dds, ig), ledger)),
                eq)))


# LAW: the sources, once they are known
law c.srcs:
  for srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for +ig: String
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  for tq: {Bool.pick(List<&2, M.Tool>, tm, ts, tts) == ts : List<&2, M.Tool>}
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss,
      es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig))) == True{} : Bool}
  {core.lhs(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""},
    Up.Tools{tts, tm, tsy, [], ""}, ig), only, g, rs) == core.rhs(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub,
      ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), g,
        ledger) : Up.Next & M.Read}

def c.srcs(
  srcs,
  dm,
  tm,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  ss,
  es,
  dsy,
  dtr,
  tts,
  tsy,
  ig,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq,
  se
):
  match srcs:
    case Up.Srcs{fs}:
      c.done(dm, tm, g, rs, only, ledger, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, fs, eq,
        ek, hw, hk, hq, tw, tk, tq)
    case Up.SrcsWait{ask}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), only, g, rs)
        == core.rhs(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm,
          dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), g, ledger) : Up.Next & M.Read}, se)
    case Up.SrcsNo{+why}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds,
        ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), only, g, rs)
        == core.rhs(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm,
          dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), g, ledger) : Up.Next & M.Read},
        mv.halt_clash(why, se))


# LAW: `.gitignore`, once it is known
law c.ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  for tq: {Bool.pick(List<&2, M.Tool>, tm, ts, tts) == ts : List<&2, M.Tool>}
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, ds, ts},
      Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}))) == True{} : Bool}
  {core.lhs(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr,
    [], ""}, Up.Tools{tts, tm, tsy, [], ""}), only, g, rs) == core.rhs(Up.got.ignore(said, srcs, M.Manifest{name,
      entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), g,
        ledger) : Up.Next & M.Read}

def c.ignore(
  said,
  srcs,
  dm,
  tm,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  ds,
  ts,
  dds,
  ss,
  es,
  dsy,
  dtr,
  tts,
  tsy,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq,
  se
):
  match said:
    case Up.Said{+ig}:
      c.srcs(srcs, dm, tm, g, rs, only, ledger, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig,
        eq, ek, hw, hk, hq, tw, tk, tq, se)
    case Up.Unsaid{+why}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), only, g, rs)
        == core.rhs(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss,
          es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), g, ledger) : Up.Next & M.Read},
        mv.halt_clash(why, se))
    case Up.Unasked{ask}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), only, g, rs)
        == core.rhs(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss,
          es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), g, ledger) : Up.Next & M.Read}, se)


# LAW: the walks, once they are done or refused
law c.pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dd.ds(dd)) == dsettle(dd.ds(dd), dd.says(Up.deps.walk(re(g,
      rs), only, M.hub.or(hub), dd.ds(dd)))) : Up.Deps}
  for hk: {Bool.or(dunc(dd), U.known(only, dd.ds(dd))) == Bool.or(dunc(dd), U.known(only, ds)) : Bool}
  for hq: {dstay(dd, ds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tt.ts(tt)) == tsettle(tt.ts(tt), tt.says(Up.tools.walk(re(g, rs), only,
      tt.ts(tt)))) : Up.Tools}
  for tk: {Bool.or(tunc(tt), M.tool.known(only, tt.ts(tt))) == Bool.or(tunc(tt), M.tool.known(only, ts)) : Bool}
  for tq: {tstay(tt, ts) == ts : List<&2, M.Tool>}
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds,
      ts}))) == True{} : Bool}
  {core.lhs(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs) == core.rhs(Up.pins(dd, tt,
    rs, M.Manifest{name, entry, bin, hub, ds, ts}), g, ledger) : Up.Next & M.Read}

def c.pins(dd, tt, g, rs, only, ledger, name, entry, bin, hub, ds, ts, eq, ek, hw, hk, hq, tw, tk, tq, se):
  match dd tt:
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}} Up.Tools{tts, tm, tsy, tasks, tbad}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}},
          Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}},
          Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}} Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}} Up.Tools{tts, tm, tsy, tasks, SNil{}}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}} Up.Tools{tts, tm, tsy, a <> as, SNil{}}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}},
          Up.Tools{tts, tm, tsy, a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}},
          Up.Tools{tts, tm, tsy, a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      c.ignore(Up.text.said(rs, Up.Ignore{}), Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), dm, tm,
        g, rs, only, ledger, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy,
        eq, ek, hw, hk, hq, tw, tk, tq, se)


# LAW: once `--package` is known to name something
law c.known:
  for k: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == k : Bool}
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds,
      ts}))) == True{} : Bool}
  {core.lhs(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs) == core.rhs(Up.known(k,
    only, rs, M.Manifest{name, entry, bin, hub, ds, ts}), g, ledger) : Up.Next & M.Read}

def c.known(k, g, rs, only, ledger, name, entry, bin, hub, ds, ts, eq, ek, se):
  match k:
    case False{}:
      Eq.bit.absurd(&2, {core.lhs(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, ds, ts}), only, g, rs)
        == core.rhs(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, ds, ts}), g,
          ledger) : Up.Next & M.Read},
        mv.halt_clash("ez: no dependency or tool named " ++ only, se))
    case True{}:
      c.pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), g, rs, only, ledger,
        name, entry, bin, hub, ds, ts, eq, ek,
        w.all(g, rs, only, M.hub.or(hub), ds), kd.known(rs, only, M.hub.or(hub), ds),
        dq.all(rs, only, M.hub.or(hub), ds),
        tw.all(g, rs, only, ts), tkd.known(rs, only, ts), tq.all(rs, only, ts), se)

# LAW: an upgrade that does not stop is decided again, on the ledger it
# left, against the same remote, as its target, and its lock was made from
# the ledger it wrote, read
law core:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +g: String
  for +ledger: Maybe<&2, String>
  for eq: {W.parsed(ledger) == r : M.Read}
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  {core.lhs(Up.next(only, r, rs), only, g, rs) == core.rhs(Up.next(only, r, rs), g, ledger)
    : Up.Next & M.Read}

def core(r, only, rs, g, ledger, eq, se):
  match r:
    case M.Bad{+why}:
      Equal.cong(M.Read, Up.Next & M.Read, x => (Up.plain(M.Bad{why}), x), M.Bad{why}, W.parsed(ledger),
        Equal.sym(M.Read, W.parsed(ledger), M.Bad{why}, eq))
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +ds, +ts}:
          c.known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), g, rs, only, ledger, name, entry,
            bin, hub, ds, ts, eq, {==}, se)

# The `.gitignore` the first upgrade left is in sync with the ledger it left,
# so the second writes none: it is the file it read, which the first found in
# sync, or the file `I.sync` made, which `I.sync` leaves as it is
# (`ML.sync_idempotent`), for a ledger whose vendored hashes hold no newline.

# whether the `.gitignore` an upgrade of a ledger model writes, given the one
# it reads, is no write at all, for a ledger whose vendored hashes hold no
# newline
def gi.ok(+model: M.Read, +g: String) -> Bool:
  +ds = Laws.ledger.deps(model)
  Bool.or(Bool.not(Str.clear.all(I.vended(ds), '\n')), List.is_empty(&2, Up.Edit, gi.of(model, g)))


# LAW: the file `I.sync` made is in sync, when no vendored hash holds a newline
law g.sync.cv:
  for cv: Bool
  for +dds: List<&2, M.Dep>
  for +ig: String
  for +ecv: {Str.clear.all(I.vended(dds), '\n') == cv : Bool}
  {Bool.or(Bool.not(cv),
    List.is_empty(&2, Up.Edit, Up.edit.if(String.eq(I.sync(dds, I.sync(dds, ig)), I.sync(dds, ig)),
      ".gitignore", I.sync(dds, I.sync(dds, ig)), []))) == True{} : Bool}

def g.sync.cv(cv, dds, ig, ecv):
  match cv:
    case False{}:
      {==}
    case True{}:
      si = Equal.sym(String, I.sync(dds, I.sync(dds, ig)), I.sync(dds, ig), ML.sync_idempotent(dds, ig, ecv))
      %si : {Bool.or(False{}, List.is_empty(&2, Up.Edit, Up.edit.if(String.eq(_, I.sync(dds, ig)),
        ".gitignore", _, []))) == True{} : Bool}
      ns = Equal.sym(Bool, String.eq(I.sync(dds, ig), I.sync(dds, ig)), True{}, Eq.string_eq_self(I.sync(dds, ig)))
      %ns : {Bool.or(False{}, List.is_empty(&2, Up.Edit, Up.edit.if(_, ".gitignore", I.sync(dds, ig), [])))
        == True{} : Bool}
      {==}

# LAW: the allowlist of the file `I.sync` made, or of one it found in sync, is
# in sync
law g.sync.b:
  for b: Bool
  for +dds: List<&2, M.Dep>
  for +ig: String
  for eb: {String.eq(I.sync(dds, ig), ig) == b : Bool}
  {Bool.or(Bool.not(Str.clear.all(I.vended(dds), '\n')),
    List.is_empty(&2, Up.Edit, Up.edit.if(
      String.eq(I.sync(dds, Laws.ig.left(Up.edit.if(b, ".gitignore", I.sync(dds, ig), []), ig)),
        Laws.ig.left(Up.edit.if(b, ".gitignore", I.sync(dds, ig), []), ig)), ".gitignore",
      I.sync(dds, Laws.ig.left(Up.edit.if(b, ".gitignore", I.sync(dds, ig), []), ig)), [])))
    == True{} : Bool}

def g.sync.b(b, dds, ig, eb):
  match b:
    case True{}:
      neb = Equal.sym(Bool, String.eq(I.sync(dds, ig), ig), True{}, eb)
      %neb : {Bool.or(Bool.not(Str.clear.all(I.vended(dds), '\n')),
        List.is_empty(&2, Up.Edit, Up.edit.if(_, ".gitignore", I.sync(dds, ig), []))) == True{} : Bool}
      mv.or_r(Bool.not(Str.clear.all(I.vended(dds), '\n')), True{}, {==})
    case False{}:
      g.sync.cv(Str.clear.all(I.vended(dds), '\n'), dds, ig, {==})



# LAW: whether a pin moved: the ledger it leaves vendors the hashes the
# allowlist was synced with
law g.done:
  for dm: Bool
  for tm: Bool
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for +ig: String
  for +fs: List<&2, Up.Found>
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  {gi.ok(Up.next.model(Up.done(M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""},
    Up.Tools{tts, tm, tsy, [], ""}, ig, fs)), Laws.ig.left(Up.next.edits(Up.done(M.Manifest{name, entry, bin, hub, ds,
      ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig, fs)), ig)) == True{} : Bool}

def g.done(dm, tm, name, entry, bin, hub, _ds, ts, dds, _ss, _es, _dsy, _dtr, _tts, _tsy, ig, _fs, hq):
  match dm:
    case True{}:
      g.sync.b(String.eq(I.sync(dds, ig), ig), dds, ig, {==})
    case False{}:
      match tm:
        case True{}:
          g.sync.b(String.eq(I.sync(dds, ig), ig), dds, ig, {==})
        case False{}:
          %hq : {gi.ok(M.Good{M.Manifest{name, entry, bin, hub, _, ts}},
            Laws.ig.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []), ig))
            == True{} : Bool}
          g.sync.b(String.eq(I.sync(dds, ig), ig), dds, ig, {==})

# LAW: the sources, once they are known
law g.srcs:
  for srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for +ig: String
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss,
      es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr,
    [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)), Laws.ig.left(Up.next.edits(Up.got.srcs(srcs, M.Manifest{name,
      entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)),
        ig)) == True{} : Bool}

def g.srcs(srcs, dm, tm, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, hq, se):
  match srcs:
    case Up.Srcs{fs}:
      g.done(dm, tm, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, fs, hq)
    case Up.SrcsWait{ask}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)),
          Laws.ig.left(Up.next.edits(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, ds, ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)), ig)) == True{} : Bool},
              se)
    case Up.SrcsNo{+why}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)),
          Laws.ig.left(Up.next.edits(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, ds, ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig)), ig)) == True{} : Bool},
              mv.halt_clash(why, se))

# LAW: `.gitignore`, once it is known
law g.ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Tool>
  for +tsy: List<&2, String>
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, ds, ts},
      Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm,
    dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})), Laws.ig.left(Up.next.edits(Up.got.ignore(said, srcs,
      M.Manifest{name, entry, bin, hub, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy,
        [], ""})), Laws.ig.said(said))) == True{} : Bool}

def g.ignore(said, srcs, dm, tm, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, hq, se):
  match said:
    case Up.Said{+ig}:
      g.srcs(srcs, dm, tm, name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, ig, hq, se)
    case Up.Unsaid{+why}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, ds,
        ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
          Laws.ig.left(Up.next.edits(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, ds, ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
              Laws.ig.said(Up.Unsaid{why}))) == True{} : Bool}, mv.halt_clash(why, se))
    case Up.Unasked{ask}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub,
        ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
          Laws.ig.left(Up.next.edits(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub, ds, ts},
            Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""})),
              Laws.ig.said(Up.Unasked{ask}))) == True{} : Bool}, se)


# LAW: the walks, once they are done or refused
law g.pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for hq: {dstay(dd, ds) == ds : List<&2, M.Dep>}
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds,
      ts}))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
    Laws.ig.left(Up.next.edits(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
      Laws.ig.read(rs))) == True{} : Bool}

def g.pins(dd, tt, rs, name, entry, bin, hub, ds, ts, hq, se):
  match dd tt:
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}} Up.Tools{tts, tm, tsy, tasks, tbad}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}},
        Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
          Laws.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}}, Up.Tools{tts, tm,
            tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, ds, ts})), Laws.ig.read(rs))) == True{} : Bool},
              se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}} Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}}, Up.Tools{tts,
        tm, tsy, tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
          Laws.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}}, Up.Tools{tts, tm, tsy,
            tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
              Laws.ig.read(rs))) == True{} : Bool}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}} Up.Tools{tts, tm, tsy, tasks, SNil{}}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}},
        Up.Tools{tts, tm, tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
          Laws.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}}, Up.Tools{tts, tm,
            tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
              Laws.ig.read(rs))) == True{} : Bool}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}} Up.Tools{tts, tm, tsy, a <> as, SNil{}}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}}, Up.Tools{tts, tm,
        tsy, a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
          Laws.ig.left(Up.next.edits(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}}, Up.Tools{tts, tm, tsy,
            a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, ds, ts})), Laws.ig.read(rs))) == True{} : Bool}, se)
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      g.ignore(Up.text.said(rs, Up.Ignore{}), Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), dm, tm,
        name, entry, bin, hub, ds, ts, dds, ss, es, dsy, dtr, tts, tsy, hq, se)


# LAW: once `--package` is known to name something
law g.known:
  for k: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds,
      ts}))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
    Laws.ig.left(Up.next.edits(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
      Laws.ig.read(rs))) == True{} : Bool}

def g.known(k, rs, only, name, entry, bin, hub, ds, ts, se):
  match k:
    case False{}:
      Eq.bit.absurd(&2, {gi.ok(Up.next.model(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
        Laws.ig.left(Up.next.edits(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, ds, ts})),
          Laws.ig.read(rs))) == True{} : Bool}, mv.halt_clash("ez: no dependency or tool named " ++ only, se))
    case True{}:
      g.pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), rs, name, entry, bin, hub,
        ds, ts, dq.all(rs, only, M.hub.or(hub), ds), se)

# LAW: an upgrade that does not stop leaves a `.gitignore` in sync with the
# ledger it leaves, for a ledger whose vendored hashes hold no newline
law g.top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  {gi.ok(Up.next.model(Up.next(only, r, rs)), Laws.ig.left(Up.next.edits(Up.next(only, r, rs)),
    Laws.ig.read(rs))) == True{} : Bool}

def g.top(r, only, rs, se):
  match r:
    case M.Bad{why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +ds, +ts}:
          g.known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), rs, only, name, entry, bin, hub, ds, ts,
            se)

# ---------------------------------------------------------------------------
# the plan of the second upgrade

# LAW: a decision and its view agree on everything but what they say
law view_model:
  for nx: Up.Next
  {Up.next.model(view(nx)) == Up.next.model(nx) : M.Read}

def view_model(nx):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, vs, sy, ed, fd, dr, sw}:
      {==}

law view_read:
  for nx: Up.Next
  {Up.next.read(view(nx)) == Up.next.read(nx) : M.Read}

def view_read(nx):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, vs, sy, ed, fd, dr, sw}:
      {==}

# LAW: what the lock may depend on is the same through the view
law view_inputs:
  for nx: Up.Next
  for listing: W.Listing
  for replies: List<&2, W.Reply>
  {W.inputs.of(view(nx), listing, replies) == W.inputs.of(nx, listing, replies) : W.Inputs}

def view_inputs(nx, _listing, _replies):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, vs, sy, ed, fd, dr, sw}:
      {==}

# LAW: and so is every path a plan leaves: what a person is told writes none
law view_put:
  for nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for +p: String
  {P.put.plan(P.made(view(nx), cs, js, d), p) == P.put.plan(P.made(nx, cs, js, d), p) : P.Wrote}

def view_put(nx, cs, js, d, p):
  match nx:
    case Up.Next{mo, rd, st, ak, tr, +vs, sy, +ed, +fd, +dr, +sw}:
      match d:
        case P.Doc{+text}:
          Equal.sym(P.Wrote,
            P.put.in(P.says.of(sy, P.lays(cs, vs, js, P.edits.of(ed, P.edits.of(Up.edit.sources(fd, sw),
              P.drops.of(dr, [P.Write{P.lockfile(), text}]))))), p),
            P.put.in(P.lays(cs, vs, js, P.edits.of(ed, P.edits.of(Up.edit.sources(fd, sw),
              P.drops.of(dr, [P.Write{P.lockfile(), text}])))), p),
            says_put(sy, P.lays(cs, vs, js, P.edits.of(ed, P.edits.of(Up.edit.sources(fd, sw),
              P.drops.of(dr, [P.Write{P.lockfile(), text}])))), p))
        case P.Stop{_why}:
          {==}

# LAW: judging a list of answers is judging each part
law judge_append:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for xs: List<&2, W.Reply>
  for +ys: List<&2, W.Reply>
  {W.judge(orgs, hub, List.append(&2, W.Reply, xs, ys))
    == List.append(&2, W.Judged, W.judge(orgs, hub, xs), W.judge(orgs, hub, ys)) : List<&2, W.Judged>}

def judge_append(orgs, hub, xs, ys):
  match xs:
    case []:
      {==}
    case W.Reply{+ask, +a} <> t:
      Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
        js => W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)} <> js,
        W.judge(orgs, hub, List.append(&2, W.Reply, t, ys)),
        List.append(&2, W.Judged, W.judge(orgs, hub, t), W.judge(orgs, hub, ys)),
        judge_append(orgs, hub, t, ys))

# LAW: a string that is empty is ""
law empty_nil:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {s == "" : String}

def empty_nil(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Eq.bit.absurd(&2, {SCon{h, t} == "" : String}, e)

# LAW: a list that is empty is []
law edits_nil:
  for es: List<&2, Up.Edit>
  for e: {List.is_empty(&2, Up.Edit, es) == True{} : Bool}
  {es == [] : List<&2, Up.Edit>}

def edits_nil(es, e):
  match es:
    case []:
      {==}
    case h <> t:
      Eq.bit.absurd(&2, {h <> t == [] : List<&2, Up.Edit>}, e)

# LAW: the target's inputs, with every tree read from BEND_LIB, are the first
# run's
law after_inputs.rest:
  for +nx1: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for es: {Up.next.stop(nx1) == "" : String}
  {W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing),
    W.judge(W.next.origins(nx1), W.next.hub(nx1),
      Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies)))}
    == W.inputs.of(nx1, listing, replies) : W.Inputs}

def after_inputs.rest(nx1, listing, replies, es):
  +o = W.next.origins(nx1)
  +h = W.next.hub(nx1)
  +laid = W.laid.replies(Up.next.trees(nx1), o, h)
  Equal.trans(W.Inputs,
    W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing),
      W.judge(o, h, Laws.after.all(o, h, List.append(&2, W.Reply, laid, replies)))},
    W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing),
      List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies))},
    W.inputs.of(nx1, listing, replies),
    Equal.cong(List<&2, W.Judged>, W.Inputs,
      js => W.Inputs{Up.next.read(nx1), "", W.listing.of(nx1, listing), js},
      W.judge(o, h, Laws.after.all(o, h, List.append(&2, W.Reply, laid, replies))),
      List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies)),
      Equal.trans(List<&2, W.Judged>,
        W.judge(o, h, Laws.after.all(o, h, List.append(&2, W.Reply, laid, replies))),
        W.judge(o, h, List.append(&2, W.Reply, laid, replies)),
        List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies)),
        after_judged(o, h, List.append(&2, W.Reply, laid, replies)),
        judge_append(o, h, laid, replies))),
    Equal.cong(String, W.Inputs,
      s => W.Inputs{Up.next.read(nx1), s, W.listing.of(nx1, listing),
        List.append(&2, W.Judged, W.judge(o, h, laid), W.judge(o, h, replies))},
      "", Up.next.stop(nx1), Equal.sym(String, Up.next.stop(nx1), "", es)))

# LAW: the second upgrade's lock reads what the first one's did: the ledger
# the first wrote, read, which it decided the target on, no refusal, the
# sources as the first left them, and every tree it read, now from BEND_LIB
law after_inputs:
  for +nx1: Up.Next
  for nx2: Up.Next
  for +g: String
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for e2: {view(nx2) == target(Up.next.read(nx1), g) : Up.Next}
  for es: {Up.next.stop(nx1) == "" : String}
  {W.inputs.of(nx2, W.listing.of(nx1, listing),
    Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies)))
    == W.inputs.of(nx1, listing, replies) : W.Inputs}

def after_inputs(nx1, nx2, g, listing, replies, e2, es):
  Equal.trans(W.Inputs,
    W.inputs.of(nx2, W.listing.of(nx1, listing),
      Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
    W.inputs.of(target(Up.next.read(nx1), g), W.listing.of(nx1, listing),
      Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
    W.inputs.of(nx1, listing, replies),
    Equal.trans(W.Inputs,
      W.inputs.of(nx2, W.listing.of(nx1, listing),
        Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
      W.inputs.of(view(nx2), W.listing.of(nx1, listing),
        Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
      W.inputs.of(target(Up.next.read(nx1), g), W.listing.of(nx1, listing),
        Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
      Equal.sym(W.Inputs,
        W.inputs.of(view(nx2), W.listing.of(nx1, listing),
          Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
        W.inputs.of(nx2, W.listing.of(nx1, listing),
          Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
        view_inputs(nx2, W.listing.of(nx1, listing),
          Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies)))),
      Equal.cong(Up.Next, W.Inputs,
        x => W.inputs.of(x, W.listing.of(nx1, listing),
          Laws.after.all(W.next.origins(nx1), W.next.hub(nx1), W.replies.of(nx1, replies))),
        view(nx2), target(Up.next.read(nx1), g), e2)),
    after_inputs.rest(nx1, listing, replies, es))

# LAW: a `.gitignore` write leaves every other path as it was
law gi_put.one:
  for +s: String
  for +p: String
  for wr: P.Wrote
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  {P.put.one(P.Write{".gitignore", s}, p, wr) == wr : P.Wrote}

def gi_put.one(s, p, wr, ng):
  match wr:
    case P.Kept{}:
      nng = Equal.sym(Bool, String.eq(".gitignore", p), False{}, ng)
      %nng : {Bool.pick(P.Wrote, _, P.Put{s}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}
    case P.Put{l}:
      {==}

law gi_put.b:
  for b: Bool
  for +s: String
  for +rest: List<&2, P.Effect>
  for +p: String
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  {P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", s, []), rest), p) == P.put.in(rest, p) : P.Wrote}

def gi_put.b(b, s, rest, p, ng):
  match b:
    case True{}:
      {==}
    case False{}:
      gi_put.one(s, p, P.put.in(rest, p), ng)

# LAW: so does the `.gitignore` an upgrade of a model writes
law gi_put:
  for md: M.Read
  for +g: String
  for +rest: List<&2, P.Effect>
  for +p: String
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  {P.put.in(P.edits.of(gi.of(md, g), rest), p) == P.put.in(rest, p) : P.Wrote}

def gi_put(md, g, rest, p, ng):
  match md:
    case M.Bad{_why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{_n, _e, _b, _h, +ds, _ts}:
          gi_put.b(String.eq(I.sync(ds, g), g), I.sync(ds, g), rest, p, ng)

# LAW: the lock's write leaves every other path as it was
law lock_put:
  for +text: String
  for +p: String
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.in([P.Write{P.lockfile(), text}], p) == P.Kept{} : P.Wrote}

def lock_put(text, p, nl):
  nnl = Equal.sym(Bool, String.eq("ez.lock.toml", p), False{}, nl)
  %nnl : {Bool.pick(P.Wrote, _, P.Put{text}, P.Kept{}) == P.Kept{} : P.Wrote}
  {==}

# LAW: the target's plan writes no path but the lock and `.gitignore`
law target_put:
  for +md: M.Read
  for +g: String
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for +p: String
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.made(target(md, g), cs, js, d), p) == P.Kept{} : P.Wrote}

def target_put(md, g, cs, js, d, p, ng, nl):
  match d:
    case P.Doc{+text}:
      Equal.trans(P.Wrote,
        P.put.in(P.lays(cs, vends.of(md), js, P.edits.of(gi.of(md, g), [P.Write{P.lockfile(), text}])), p),
        P.put.in(P.edits.of(gi.of(md, g), [P.Write{P.lockfile(), text}]), p),
        P.Kept{},
        lays_put(cs, vends.of(md), js, P.edits.of(gi.of(md, g), [P.Write{P.lockfile(), text}]), p),
        Equal.trans(P.Wrote,
          P.put.in(P.edits.of(gi.of(md, g), [P.Write{P.lockfile(), text}]), p),
          P.put.in([P.Write{P.lockfile(), text}], p),
          P.Kept{},
          gi_put(md, g, [P.Write{P.lockfile(), text}], p, ng),
          lock_put(text, p, nl)))
    case P.Stop{_why}:
      {==}

# LAW: and when it writes no `.gitignore`, no path but the lock
law target_put.clean:
  for +md: M.Read
  for +g: String
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for +p: String
  for eg: {gi.of(md, g) == [] : List<&2, Up.Edit>}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.made(target(md, g), cs, js, d), p) == P.Kept{} : P.Wrote}

def target_put.clean(md, g, cs, js, d, p, eg, nl):
  match d:
    case P.Doc{+text}:
      neg = Equal.sym(List<&2, Up.Edit>, gi.of(md, g), [], eg)
      %neg : {P.put.plan(P.made(Up.Next{md, md, "", [], [], vends.of(md), [], _, [], [], []}, cs, js, P.Doc{text}), p)
        == P.Kept{} : P.Wrote}
      Equal.trans(P.Wrote,
        P.put.in(P.lays(cs, vends.of(md), js, [P.Write{P.lockfile(), text}]), p),
        P.put.in([P.Write{P.lockfile(), text}], p),
        P.Kept{},
        lays_put(cs, vends.of(md), js, [P.Write{P.lockfile(), text}], p),
        lock_put(text, p, nl))
    case P.Stop{_why}:
      {==}

def core.fst(q: Up.Next & M.Read) -> Up.Next:
  (a, _b) = q
  a

def core.snd(q: Up.Next & M.Read) -> M.Read:
  (_a, b) = q
  b

# ---------------------------------------------------------------------------
# `ez lock --upgrade`, run again (EZ-DOC-4)

# LAW: an upgrade that does not refuse leaves the World `after.up.laid` says
law u.after:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  {Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
    ups}) == Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : W.World}

def u.after(only, ledger, listing, replies, ups, ok):
  nok = Equal.sym(Bool, P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), False{}, ok)
  %nok : {Laws.after.up.pick(_, W.World{W.Args{True{}, only}, ledger, listing, replies,
    ups}) == Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : W.World}
  {==}

# LAW: the ledger it wrote reads back as the model it rendered
law u.rb:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
    ledger)) == Up.next.model(Up.next(only, W.parsed(ledger), ups)) : M.Read}

def u.rb(only, ledger, listing, replies, ups, ok, rb):
  Equal.trans(M.Read, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
    W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}))),
      Up.next.model(Up.next(only, W.parsed(ledger), ups)),
    Equal.cong(W.World, M.Read, x => W.parsed(W.ledger.of(x)), Laws.after.up.laid(W.World{W.Args{True{}, only},
      ledger, listing, replies, ups}), Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
      Equal.sym(W.World, Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
        Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), u.after(only, ledger,
          listing, replies, ups, ok))),
    rb)

# LAW: it did not stop
law u.se:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  {String.is_empty(Up.next.stop(Up.next(only, W.parsed(ledger), ups))) == True{} : Bool}

def u.se(only, ledger, listing, replies, ups, ok):
  mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok)

# LAW: the second upgrade decides the target
law u.e2:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {view(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
    re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)),
      ups))) == target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), Laws.ig.read(ups))) : Up.Next}

def u.e2(only, ledger, listing, replies, ups, ok, rb):
  Equal.trans(Up.Next, view(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
    ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
      view(Up.next(only, Up.next.model(Up.next(only, W.parsed(ledger), ups)),
        re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
          target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
            W.parsed(ledger), ups)), Laws.ig.read(ups))),
    Equal.cong(M.Read, Up.Next, r => view(Up.next(only, r, re(Laws.ig.left(Up.next.edits(Up.next(only,
      W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))), W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), ledger)), Up.next.model(Up.next(only, W.parsed(ledger), ups)),
      u.rb(only, ledger, listing, replies, ups, ok, rb)),
    Equal.cong(Up.Next & M.Read, Up.Next, q => core.fst(q),
      core.lhs(Up.next(only, W.parsed(ledger), ups), only, Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger),
        ups)), Laws.ig.read(ups)), ups), core.rhs(Up.next(only, W.parsed(ledger), ups),
          Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ledger),
      core(W.parsed(ledger), only, ups, Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
        Laws.ig.read(ups)), ledger, {==}, u.se(only, ledger, listing, replies, ups, ok))))

# LAW: and the first one's lock was made from its model
law u.rm:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {Up.next.read(Up.next(only, W.parsed(ledger), ups)) == Up.next.model(Up.next(only, W.parsed(ledger), ups)) : M.Read}

def u.rm(only, ledger, listing, replies, ups, ok, rb):
  Equal.trans(M.Read, Up.next.read(Up.next(only, W.parsed(ledger), ups)),
    W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
      Up.next.model(Up.next(only, W.parsed(ledger), ups)),
    Equal.cong(Up.Next & M.Read, M.Read, q => core.snd(q),
      core.lhs(Up.next(only, W.parsed(ledger), ups), only, Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger),
        ups)), Laws.ig.read(ups)), ups), core.rhs(Up.next(only, W.parsed(ledger), ups),
          Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ledger),
      core(W.parsed(ledger), only, ups, Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
        Laws.ig.read(ups)), ledger, {==}, u.se(only, ledger, listing, replies, ups, ok))),
    u.rb(only, ledger, listing, replies, ups, ok, rb))

# LAW: so the second decides the target of the ledger the first lock read
law u.e2r:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {view(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
    re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)),
      ups))) == target(Up.next.read(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), Laws.ig.read(ups))) : Up.Next}

def u.e2r(only, ledger, listing, replies, ups, ok, rb):
  Equal.trans(Up.Next, view(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
    ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
      target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), Laws.ig.read(ups))), target(Up.next.read(Up.next(only, W.parsed(ledger), ups)),
          Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups))),
    u.e2(only, ledger, listing, replies, ups, ok, rb),
    Equal.cong(M.Read, Up.Next, m => target(m, Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
      Laws.ig.read(ups))), Up.next.model(Up.next(only, W.parsed(ledger), ups)), Up.next.read(Up.next(only,
        W.parsed(ledger), ups)),
      Equal.sym(M.Read, Up.next.read(Up.next(only, W.parsed(ledger), ups)), Up.next.model(Up.next(only,
        W.parsed(ledger), ups)), u.rm(only, ledger, listing, replies, ups, ok, rb))))

# LAW: the lock, run again after an upgrade that did not refuse
law u.idem.ok:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {P.put(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
    "ez.lock.toml") == P.put(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}, "ez.lock.toml") : P.Wrote}

def u.idem.ok(only, ledger, listing, replies, ups, ok, rb):
  Laws.lock_reproducible(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
    W.World{W.Args{True{}, only}, ledger, listing, replies, ups},
    after_inputs(Up.next(only, W.parsed(ledger), ups), Up.next(only,
      W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
        re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups)),
          Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), listing, replies,
            u.e2r(only, ledger, listing, replies, ups, ok, rb),
      empty_nil(Up.next.stop(Up.next(only, W.parsed(ledger), ups)), u.se(only, ledger, listing, replies, ups, ok))))

# LAW: either way
law u.idem:
  for b: Bool
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +e: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == b : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {P.put(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
    "ez.lock.toml") == P.put(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}, "ez.lock.toml") : P.Wrote}

def u.idem(b, only, ledger, listing, replies, ups, e, rb):
  match b:
    case True{}:
      ne = Equal.sym(Bool, P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), True{}, e)
      %ne : {P.put(Laws.after.up.pick(_, W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
        "ez.lock.toml") == P.put(W.World{W.Args{True{}, only}, ledger, listing, replies, ups},
          "ez.lock.toml") : P.Wrote}
      {==}
    case False{}:
      Equal.trans(P.Wrote, P.put(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
        "ez.lock.toml"), P.put(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
          "ez.lock.toml"),
        P.put(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}, "ez.lock.toml"),
        Equal.cong(W.World, P.Wrote, x => P.put(x, "ez.lock.toml"), Laws.after(W.World{W.Args{True{}, only}, ledger,
          listing, replies, ups}), Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
          u.after(only, ledger, listing, replies, ups, e)),
        u.idem.ok(only, ledger, listing, replies, ups, e, rb))

def Laws.upgrade_idempotent(w, u, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.put(Laws.after(W.World{W.Args{False{}, only}, ledger, listing, replies, ups}),
                "ez.lock.toml") == P.put(W.World{W.Args{False{}, only}, ledger, listing, replies, ups},
                "ez.lock.toml") : P.Wrote}, u)
            case True{}:
              u.idem(P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), only, ledger, listing,
                replies, ups, {==}, rb)

# LAW: the model, either way
law u.moves:
  for b: Bool
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +e: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == b : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {P.ledger.next(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
    ups})) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}

def u.moves(b, only, ledger, listing, replies, ups, e, rb):
  match b:
    case True{}:
      ne = Equal.sym(Bool, P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), True{}, e)
      %ne : {P.ledger.next(Laws.after.up.pick(_, W.World{W.Args{True{}, only}, ledger, listing, replies,
        ups})) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
      {==}
    case False{}:
      Equal.trans(M.Read, P.ledger.next(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups})),
        P.ledger.next(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups})),
          Up.next.model(Up.next(only, W.parsed(ledger), ups)),
        Equal.cong(W.World, M.Read, x => P.ledger.next(x), Laws.after(W.World{W.Args{True{}, only}, ledger, listing,
          replies, ups}), Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
          u.after(only, ledger, listing, replies, ups, e)),
        Equal.trans(M.Read, Up.next.model(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
          W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
            Laws.ig.read(ups)), ups))), Up.next.model(view(Up.next(only,
              W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
                re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups)))),
                  Up.next.model(Up.next(only, W.parsed(ledger), ups)),
          Equal.sym(M.Read, Up.next.model(view(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
            W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
              Laws.ig.read(ups)), ups)))), Up.next.model(Up.next(only,
                W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
                  re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
                    view_model(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
                      ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                        Laws.ig.read(ups)), ups)))),
          Equal.cong(Up.Next, M.Read, x => Up.next.model(x), view(Up.next(only,
            W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
              re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
                target(Up.next.model(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
                  W.parsed(ledger), ups)), Laws.ig.read(ups))),
            u.e2(only, ledger, listing, replies, ups, e, rb))))

def Laws.reupgrade_moves_nothing(w, u, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.ledger.next(Laws.after(W.World{W.Args{False{}, only}, ledger, listing, replies,
                ups})) == P.ledger.next(W.World{W.Args{False{}, only}, ledger, listing, replies, ups}) : M.Read}, u)
            case True{}:
              u.moves(P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), only, ledger, listing,
                replies, ups, {==}, rb)

# LAW: what the second upgrade's plan leaves at a path, through its view
law u.put:
  for +nx2: Up.Next
  for +listing2: W.Listing
  for +replies2: List<&2, W.Reply>
  for +md: M.Read
  for +g: String
  for +p: String
  for e: {view(nx2) == target(md, g) : Up.Next}
  for ng: {String.eq(".gitignore", p) == False{} : Bool}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.plan.of(nx2, listing2, replies2), p) == P.Kept{} : P.Wrote}

def u.put(nx2, listing2, replies2, md, g, p, e, ng, nl):
  +cs = P.cloned(W.replies.of(nx2, replies2))
  +js = W.judged.of(nx2, replies2)
  +dc = P.decide(W.Inputs{Up.next.read(nx2), Up.next.stop(nx2), W.listing.of(nx2, listing2), js})
  Equal.trans(P.Wrote, P.put.plan(P.made(nx2, cs, js, dc), p), P.put.plan(P.made(view(nx2), cs, js, dc), p),
    P.Kept{},
    Equal.sym(P.Wrote, P.put.plan(P.made(view(nx2), cs, js, dc), p), P.put.plan(P.made(nx2, cs, js, dc), p),
      view_put(nx2, cs, js, dc, p)),
    Equal.trans(P.Wrote, P.put.plan(P.made(view(nx2), cs, js, dc), p),
      P.put.plan(P.made(target(md, g), cs, js, dc), p), P.Kept{},
      Equal.cong(Up.Next, P.Wrote, x => P.put.plan(P.made(x, cs, js, dc), p), view(nx2), target(md, g), e),
      target_put(md, g, cs, js, dc, p, ng, nl)))

# LAW: and when it writes no `.gitignore`
law u.put.clean:
  for +nx2: Up.Next
  for +listing2: W.Listing
  for +replies2: List<&2, W.Reply>
  for +md: M.Read
  for +g: String
  for +p: String
  for e: {view(nx2) == target(md, g) : Up.Next}
  for eg: {gi.of(md, g) == [] : List<&2, Up.Edit>}
  for nl: {String.eq("ez.lock.toml", p) == False{} : Bool}
  {P.put.plan(P.plan.of(nx2, listing2, replies2), p) == P.Kept{} : P.Wrote}

def u.put.clean(nx2, listing2, replies2, md, g, p, e, eg, nl):
  +cs = P.cloned(W.replies.of(nx2, replies2))
  +js = W.judged.of(nx2, replies2)
  +dc = P.decide(W.Inputs{Up.next.read(nx2), Up.next.stop(nx2), W.listing.of(nx2, listing2), js})
  Equal.trans(P.Wrote, P.put.plan(P.made(nx2, cs, js, dc), p), P.put.plan(P.made(view(nx2), cs, js, dc), p),
    P.Kept{},
    Equal.sym(P.Wrote, P.put.plan(P.made(view(nx2), cs, js, dc), p), P.put.plan(P.made(nx2, cs, js, dc), p),
      view_put(nx2, cs, js, dc, p)),
    Equal.trans(P.Wrote, P.put.plan(P.made(view(nx2), cs, js, dc), p),
      P.put.plan(P.made(target(md, g), cs, js, dc), p), P.Kept{},
      Equal.cong(Up.Next, P.Wrote, x => P.put.plan(P.made(x, cs, js, dc), p), view(nx2), target(md, g), e),
      target_put.clean(md, g, cs, js, dc, p, eg, nl)))

# LAW: an `or` of a `not` of True is its right half
law or_not_true:
  for c: Bool
  for +x: Bool
  for ec: {c == True{} : Bool}
  for e: {Bool.or(Bool.not(c), x) == True{} : Bool}
  {x == True{} : Bool}

def or_not_true(c, x, ec, e):
  match c:
    case True{}:
      e
    case False{}:
      Eq.bit.absurd(&2, {x == True{} : Bool}, ec)

def Laws.upgrade_settles(w, u, ok, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.put(Laws.after(W.World{W.Args{False{}, only}, ledger, listing, replies, ups}),
                "ez.toml") == P.Kept{} : P.Wrote}, u)
            case True{}:
              Equal.trans(P.Wrote, P.put(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
                "ez.toml"), P.put(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
                  "ez.toml"), P.Kept{},
                Equal.cong(W.World, P.Wrote, x => P.put(x, "ez.toml"), Laws.after(W.World{W.Args{True{}, only},
                  ledger, listing, replies, ups}), Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing,
                    replies, ups}),
                  u.after(only, ledger, listing, replies, ups, ok)),
                u.put(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                  ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)),
                    ups)), W.listing.of(Up.next(only, W.parsed(ledger), ups), listing),
                  Laws.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
                    W.parsed(ledger), ups)), W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)),
                  Up.next.model(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
                    W.parsed(ledger), ups)), Laws.ig.read(ups)), "ez.toml", u.e2(only, ledger, listing, replies, ups,
                      ok, rb), {==}, {==}))

def Laws.reupgrade_writes_only_lock(w, p, u, ok, rb, ev, ne):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {P.put(Laws.after(W.World{W.Args{False{}, only}, ledger, listing, replies, ups}),
                p) == P.Kept{} : P.Wrote}, u)
            case True{}:
              Equal.trans(P.Wrote, P.put(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), p),
                P.put(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}), p), P.Kept{},
                Equal.cong(W.World, P.Wrote, x => P.put(x, p), Laws.after(W.World{W.Args{True{}, only}, ledger,
                  listing, replies, ups}), Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies,
                    ups}),
                  u.after(only, ledger, listing, replies, ups, ok)),
                u.put.clean(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger),
                  ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                    Laws.ig.read(ups)), ups)), W.listing.of(Up.next(only, W.parsed(ledger), ups), listing),
                  Laws.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
                    W.parsed(ledger), ups)), W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)),
                  Up.next.model(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
                    W.parsed(ledger), ups)), Laws.ig.read(ups)), p, u.e2(only, ledger, listing, replies, ups, ok, rb),
                  edits_nil(gi.of(Up.next.model(Up.next(only, W.parsed(ledger), ups)),
                    Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups))),
                    or_not_true(Str.clear.all(I.vended(Laws.ledger.deps(Up.next.model(Up.next(only, W.parsed(ledger),
                      ups)))), '\n'),
                      List.is_empty(&2, Up.Edit, gi.of(Up.next.model(Up.next(only, W.parsed(ledger), ups)),
                        Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)))), ev,
                      g.top(W.parsed(ledger), only, ups, u.se(only, ledger, listing, replies, ups, ok)))),
                  ne))

# LAW: the second upgrade reads each tree the first laid from BEND_LIB
law u.fresh:
  for +only: String
  for +ledger: Maybe<&2, String>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +ups: List<&2, Up.Reply>
  for +ok: {P.refuses(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) == False{} : Bool}
  for +rb: {W.parsed(W.ledger.of(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies,
      ups}))) == P.ledger.next(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}) : M.Read}
  {Laws.fresh(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups})) == [] : List<&2, String>}

def u.fresh(only, ledger, listing, replies, ups, ok, rb):
  +rs1 = W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)
  +er = Equal.trans(M.Read, Up.next.read(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
    W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
      Laws.ig.read(ups)), ups))), Up.next.read(view(Up.next(only,
        W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
          re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups)))),
            Up.next.read(Up.next(only, W.parsed(ledger), ups)),
    Equal.sym(M.Read, Up.next.read(view(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
      W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
        Laws.ig.read(ups)), ups)))), Up.next.read(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
          W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
            Laws.ig.read(ups)), ups))), view_read(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
              W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
                Laws.ig.read(ups)), ups)))),
    Equal.cong(Up.Next, M.Read, x => Up.next.read(x), view(Up.next(only,
      W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
        re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
          target(Up.next.read(Up.next(only, W.parsed(ledger), ups)), Laws.ig.left(Up.next.edits(Up.next(only,
            W.parsed(ledger), ups)), Laws.ig.read(ups))),
      u.e2r(only, ledger, listing, replies, ups, ok, rb)))
  Equal.trans(List<&2, String>, Laws.fresh(Laws.after(W.World{W.Args{True{}, only}, ledger, listing, replies, ups})),
    Laws.fresh(Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups})), [],
    Equal.cong(W.World, List<&2, String>, x => Laws.fresh(x), Laws.after(W.World{W.Args{True{}, only}, ledger,
      listing, replies, ups}), Laws.after.up.laid(W.World{W.Args{True{}, only}, ledger, listing, replies, ups}),
      u.after(only, ledger, listing, replies, ups, ok)),
    Equal.trans(List<&2, String>,
      Laws.fresh.all(L.ledger.read(Up.next.read(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only,
        W.parsed(ledger), ups)), ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
          Laws.ig.read(ups)), ups)))), M.hub_of(Up.next.read(Up.next(only,
            W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), ledger)),
              re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups)))),
        Laws.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
          W.parsed(ledger), ups)), rs1)),
      Laws.fresh.all(L.ledger.read(Up.next.read(Up.next(only, W.parsed(ledger), ups))),
        M.hub_of(Up.next.read(Up.next(only, W.parsed(ledger), ups))),
        Laws.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
          W.parsed(ledger), ups)), rs1)),
      [],
      Equal.cong(M.Read, List<&2, String>,
        r => Laws.fresh.all(L.ledger.read(r), M.hub_of(r),
          Laws.after.all(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only,
            W.parsed(ledger), ups)), rs1)),
        Up.next.read(Up.next(only, W.parsed(Laws.ledger.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)),
          ledger)), re(Laws.ig.left(Up.next.edits(Up.next(only, W.parsed(ledger), ups)), Laws.ig.read(ups)), ups))),
            Up.next.read(Up.next(only, W.parsed(ledger), ups)), er),
      fresh.all_after(W.next.origins(Up.next(only, W.parsed(ledger), ups)), W.next.hub(Up.next(only, W.parsed(ledger),
        ups)), rs1)))

def Laws.reupgrade_lays_nothing(w, u, ok, rb):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{up, +only}:
          match up:
            case False{}:
              Eq.bit.absurd(&2, {Laws.fresh(Laws.after(W.World{W.Args{False{}, only}, ledger, listing, replies,
                ups})) == [] : List<&2, String>}, u)
            case True{}:
              u.fresh(only, ledger, listing, replies, ups, ok, rb)

# No ledger reads as a `Bad`, which a plain lock takes as it is and an
# upgrade leaves as it is, and `need.why` refuses it.
def Laws.lock_needs_ledger(up, _only, _listing, _rs, _us):
  match up:
    case True{}:
      {==}
    case False{}:
      {==}

# The same once the read is rewritten to the `Bad` the premise gives.
def Laws.lock_refuses_unread(up, only, _s, listing, rs, us, _why, bad):
  match up:
    case True{}:
      %bad : {P.refuses.doc(P.decide(W.inputs.of(Up.next(only, _, us), listing, rs))) == True{}
        : Bool}
      {==}
    case False{}:
      %bad : {P.refuses.doc(P.decide(W.inputs.of(Up.plain(_), listing, rs))) == True{}
        : Bool}
      {==}
