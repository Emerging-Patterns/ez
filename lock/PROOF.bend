# lock: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import ../manifest/manifest.bend as M
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../pkg/pkg.bend as K
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

# The planner. A plan's effects are the cloned trees laid, then the lock
# written; a lay writes no path a law names, so what the plan leaves at a path
# is what the planner decided.

# LAW: one tree laid, or passed over, leaves every path as it was
law pick_put:
  for b: Bool
  for v: W.Verdict
  for +h: String
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.lay.pick(b, v, h, rest), p) == P.put.in(rest, p) : P.Wrote}

def pick_put(b, v, _h, _rest, _p):
  match b:
    case True{}:
      match v:
        case W.No{_why}:
          {==}
        case W.Ok{fs, ss}:
          {==}
    case False{}:
      {==}

# LAW: and so do all of them
law lays_put:
  for +cs: List<&2, String>
  for js: List<&2, W.Judged>
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.lays(cs, js, rest), p) == P.put.in(rest, p) : P.Wrote}

def lays_put(cs, js, rest, p):
  match js:
    case []:
      {==}
    case W.Judged{+h, +v} <> +t:
      Equal.trans(P.Wrote,
        P.put.in(P.lay.pick(L.seen.holds(cs, h), v, h, P.lays(cs, t, rest)), p),
        P.put.in(P.lays(cs, t, rest), p),
        P.put.in(rest, p),
        pick_put(L.seen.holds(cs, h), v, h, P.lays(cs, t, rest), p),
        lays_put(cs, t, rest, p))

# LAW: what a plan leaves at the lock's path is what the planner decided
law made_put:
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  {P.put.plan(P.made(cs, js, d), "ez.lock.toml") == Laws.put.doc(d) : P.Wrote}

def made_put(cs, js, d):
  match d:
    case P.Doc{text}:
      lays_put(cs, js, [P.Write{P.lockfile(), text}], "ez.lock.toml")
    case P.Stop{_why}:
      {==}

# LAW: and at ez.toml it leaves nothing, whatever was decided
law made_keeps_ledger:
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  {P.put.plan(P.made(cs, js, d), "ez.toml") == P.Kept{} : P.Wrote}

def made_keeps_ledger(cs, js, d):
  match d:
    case P.Doc{text}:
      lays_put(cs, js, [P.Write{P.lockfile(), text}], "ez.toml")
    case P.Stop{_why}:
      {==}

# LAW: what plain `ez lock` writes to its lock is a function of what the
# planner decided over the World's Inputs
law put_decides:
  for w: W.World
  {P.put(w, "ez.lock.toml") == Laws.put.doc(P.decide(W.inputs(w))) : P.Wrote}

def put_decides(w):
  match w:
    case W.World{_args, +ledger, listing, +replies}:
      made_put(P.cloned(replies),
        W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
        P.decide(W.Inputs{ledger, listing,
          W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)}))

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
    case W.World{_args, +ledger, listing, replies}:
      Equal.cong(List<&2, W.Judged>, W.Inputs,
        js => W.Inputs{ledger, listing, js},
        W.judge(W.origins(ledger), W.ledger.hub(ledger),
          W.reclone.all(W.origins(ledger), replies)),
        W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
        reclone_judged(W.origins(ledger), W.ledger.hub(ledger), replies))

def Laws.clone_reproduces(w):
  Laws.lock_reproducible(W.reclone(w), w, reclone_inputs(w))

def Laws.plain_lock_keeps_ledger(w, _e):
  match w:
    case W.World{_args, +ledger, listing, +replies}:
      made_keeps_ledger(P.cloned(replies),
        W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
        P.decide(W.Inputs{ledger, listing,
          W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)}))

# LAW: a plan made from a refusal has no effect that writes
law made_refused:
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for r: {P.refuses.doc(d) == True{} : Bool}
  {P.writes(P.made(cs, js, d)) == False{} : Bool}

def made_refused(cs, js, d, r):
  match d:
    case P.Doc{text}:
      Eq.bit.absurd(&2, {P.writes(P.made(cs, js, P.Doc{text})) == False{} : Bool}, r)
    case P.Stop{_why}:
      {==}

def Laws.lock_refusal_writes_nothing(w, r):
  match w:
    case W.World{_args, +ledger, listing, +replies}:
      made_refused(P.cloned(replies),
        W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
        P.decide(W.Inputs{ledger, listing,
          W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)}), r)

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

def Laws.plain_lock_pins_ledger_sources(w, _e):
  match w:
    case W.World{_args, +ledger, listing, +replies}:
      match listing:
        case W.Unlisted{why}:
          {==}
        case W.Listed{fs}:
          Laws.walk_pins_ledger_sources(U32.to_nat(100000),
            L.ledger.read(W.parsed(ledger)),
            W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
            P.Walk{P.roots(fs), [], [], ""}, {==})

# `.ez/` is a prefix of anything appended to it, which `starts_append` holds,
# and that picks the arm that keeps nothing.
def Laws.root_skips_ez(p, text):
  Equal.cong(Bool, List<&2, String>,
    k => Bool.pick(List<&2, String>, k, [], L.specs(K.scan.mods(K.scan(text)))),
    String.starts_with(".ez/" ++ p, ".ez/"), True{}, Eq.starts_append(".ez/", p))

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
