# facts about what plans write, say and refuse, shared across most proofs
import Base
import ../../src/check/eq.bend as Eq
import ../../src/lock/plan.bend as P
import ../../src/pkg/pkg.bend as K
import ../../src/pkg/path.bend as Path
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/ledger/ignore.bend as I
import ../../src/pub/world.bend as PW
import ../../src/pub/plan.bend as PP
import ../../src/pub/blurb.bend as B
import ../../src/lock/lock.bend as L
import ../../src/doctor/world.bend as DW
import ../../src/doctor/plan.bend as DP
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../src/add/plan.bend as AP
import ../../src/ez/named.bend as Named
import ../../src/init/plan.bend as IP
import ../../src/remove/plan.bend as RP
import ../../src/ws/joint.bend as J
import ../../src/ez/key.bend as KKey
import ../../laws/LockReproducible.bend as L1
import ../../laws/MatchingNarHashPasses.bend as L2
import ../../laws/PlainLockWritesOnlyLock.bend as L3
import ../../laws/PublishNeedsCleanTree.bend as L4
import ../../laws/PublishSaysDescription.bend as L5
import ../../laws/RemoveDependencyIdempotent.bend as L6
import ../../laws/SkippedComponentChangesNothing.bend as L7
import ../../laws/ImportHashIsFirstComponent.bend as L8
import ../../laws/SlashlessPathSplitsToItself.bend as L9
import ../../laws/LedgerRemoveIdempotent.bend as L10
import ../../laws/defs/LockInputs.bend as D1
import ../../laws/defs/Slashless.bend as D2

# LAW: one character of the split, with the separator test given as a
# parameter, since a match may not scrutinise a computed value
law split_plain.step:
  for +h: Char
  for +t: String
  for e: {False{} == Char.is_eq(h, '/') : Bool}
  for ih: {String.split(t, '/') == [t] : List<&2, String>}
  {String.split(SCon{h, t}, '/') == [SCon{h, t}] : List<&2, String>}

def split_plain.step(h, t, e, ih):
  %e : {String.split.fin(h, String.split(t, '/'), _) == [SCon{h, t}]
    : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>,
    r => String.split.fin(h, r, False{}),
    String.split(t, '/'), [t], ih)

# By induction on the string. A head that is not the separator is pushed onto
# the one component the tail split into, which is the tail.
def L9.split_plain(p, e):
  match p:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      split_plain.step(h, t,
        Equal.sym(Bool, Char.is_eq(h, '/'), False{},
          Eq.not.true(Char.is_eq(h, '/'),
            Eq.and.left(Bool.not(Char.is_eq(h, '/')), D2.slashless(t), e))),
        L9.split_plain(t,
          Eq.and.right(Bool.not(Char.is_eq(h, '/')), D2.slashless(t), e)))

# The leftover path and scan equalities. The closed ones reduce; the rest
# are a hypothesis rewritten into a pick, a split walked one character at
# a time, or a suffix taken off a concatenation.

def L7.skip_id(w):
  match w:
    case Path.Walk{_abs, _out}:
      {==}

# LAW: one step of the drop, with the branch the pick takes given as a
# parameter and the equation that put it there given alongside, since a match
# may not scrutinise a computed value
law without_idem.arm:
  for -h: M.Dep
  for -r: List<&2, M.Dep>
  for +name: String
  for b: Bool
  for eb: {String.eq(M.dep.name(h), name) == b : Bool}
  for ih: {Rend.without(r, name) == r : List<&2, M.Dep>}
  {Rend.without(Rend.without.put(b, h, r), name) == Rend.without.put(b, h, r)
    : List<&2, M.Dep>}

def without_idem.arm(h, r, name, b, eb, ih):
  match b:
    case True{}:
      ih
    case False{}:
      Equal.trans(List<&2, M.Dep>,
        Rend.without.put(String.eq(M.dep.name(h), name), h, Rend.without(r, name)),
        Rend.without.put(False{}, h, Rend.without(r, name)),
        h <> r,
        Equal.cong(Bool, List<&2, M.Dep>,
          x => Rend.without.put(x, h, Rend.without(r, name)),
          String.eq(M.dep.name(h), name), False{}, eb),
        Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>, y => h <> y,
          Rend.without(r, name), r, ih))

def L10.without_idem(ds, name):
  match ds:
    case []:
      {==}
    case +h <> t:
      without_idem.arm(h, Rend.without(t, name), name,
        String.eq(M.dep.name(h), name), {==}, L10.without_idem(t, name))

# The text layer of the allowlist (laws/GitignoreAllowlistIsLedger.bend).
# `I.sync` reads a file into its lines, derives the allowlist over them, and
# writes them back, each ending with a newline. A file written from lines
# that hold no newline reads back as those lines, and no line read from a
# file holds one, so the file `sync` writes reads back as the lines
# `I.lines` made, and the line laws above hold of its bytes.

# LAW: an `and` of two halves that answered True
law and_tt:
  for u: Bool
  for v: Bool
  for eu: {u == True{} : Bool}
  for ev: {v == True{} : Bool}
  {Bool.and(u, v) == True{} : Bool}

def and_tt(u, v, eu, ev):
  %Equal.sym(Bool, u, True{}, eu) : {Bool.and(_, v) == True{} : Bool}
  ev

# whether no hash of a list is one `seen` names. Law vocabulary: ez never
# calls it.
def fresh(hs: List<&2, String>, +seen: List<&2, String>) -> Bool:
  match hs:
    case []:
      True{}
    case +h <> t:
      +rest = fresh(t, seen)
      Bool.and(Bool.not(I.named(seen, h)), rest)

# the first run of the walk over a file, with the block it puts down. Law
# vocabulary: ez never calls it.
def one(+ls: List<&2, String>, blk: List<&2, String>) -> List<&2, String>:
  I.walk(I.tag(ls), I.rules(I.tag(ls)), blk, False{})

# the second run, over what the first wrote, with its own block: the rules
# the first run's output lacks, unless it has a `.ez/` line or `emp` says the
# ledger vends nothing, and then the allowlist lines `a`
def two(+ls: List<&2, String>, +blk: List<&2, String>, emp: Bool, a: List<&2, String>) -> List<&2, String>:
  +m = one(ls, blk)
  I.walk(I.tag(m), I.rules(I.tag(m)),
    List.append(&2, String, I.need(Bool.or(I.has(I.tag(m), I.Dir{}), emp), I.rules(I.tag(m))),
      a), False{})

law unsent_fails:
  for v: PP.Verdict
  for +w: PW.World
  for r: {PP.sends.v(v) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(v, w)) == False{} : Bool}

def unsent_fails(v, w, r):
  match v:
    case PP.Go{}:
      Eq.bit.absurd2(&2, {PP.succeeds.plan(PP.plan.v(PP.Go{}, w)) == False{} : Bool}, r)
    case PP.Pending{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def L4.pub_unsent_refuses(w, r):
  unsent_fails(PP.decide(w), w, r)

# ---------------------------------------------------------------------------
# the hub description

# LAW: one character of the line: a newline contradicts the premise, and any
# other character is the line's own, with the rest of the line after it
law line_first_cut.arm:
  for +h: Char
  for t: String
  for +b: String
  for c: Bool
  for one: {B.nl.step(c, _u => B.has.nl(t)) == False{} : Bool}
  for ih: {B.has.nl(t) == False{} : Bool} -> {B.line.first(t ++ "\n" ++ b) == t : String}
  {B.line.step(c, h, _u => B.line.first(t ++ "\n" ++ b)) == SCon{h, t} : String}

def line_first_cut.arm(h, t, b, c, one, ih):
  match c:
    case True{}:
      Eq.bit.absurd2(&2, {B.line.step(True{}, h, _u => B.line.first(t ++ "\n" ++ b)) == SCon{h, t} : String}, one)
    case False{}:
      Equal.cong(String, String, x => SCon{h, x}, B.line.first(t ++ "\n" ++ b), t, ih(one))

def L5.line_first_cut(a, b, one):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      line_first_cut.arm(h, t, b, Char.is_eq(h, '\n'), one, x => L5.line_first_cut(t, b, x))

# ---------------------------------------------------------------------------
# a step of a scan

# LAW: a step whose rest answers True answers True, whatever its head said
law step_true:
  for b: Bool
  for r: Unit -> Bool
  for e: {r(Unit{}) == True{} : Bool}
  {DP.has.step(b, r) == True{} : Bool}

def step_true(b, _r, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

# LAW: and so does a step whose head answered True
law step_hit:
  for b: Bool
  for r: Unit -> Bool
  for e: {b == True{} : Bool}
  {DP.has.step(b, r) == True{} : Bool}

def step_hit(b, r, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {DP.has.step(False{}, r) == True{} : Bool}, e)

# ---------------------------------------------------------------------------
# what a plan says

# LAW: a line said by the rest of the lines is said by all of them
law said_cons:
  for n: DP.Note
  for +rest: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(rest), line) == True{} : Bool}
  {DP.said.in(DP.says(n <> rest), line) == True{} : Bool}

def said_cons(n, rest, line, e):
  match n:
    case DP.Note{_w, l}:
      step_true(String.eq(l, line), _u => DP.said.in(DP.says(rest), line), e)

# LAW: and a line said by the last lines is said by all of them
law said_append:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(b), line) == True{} : Bool}
  {DP.said.in(DP.says(List.append(&2, DP.Note, a, b)), line) == True{} : Bool}

def said_append(a, b, line, e):
  match a:
    case []:
      e
    case h <> +t:
      said_cons(h, List.append(&2, DP.Note, t, b), line, said_append(t, b, line, e))

# LAW: a report with a problem in its last part has a problem
law wrong_append:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for e: {DP.wrong(b) == True{} : Bool}
  {DP.wrong(List.append(&2, DP.Note, a, b)) == True{} : Bool}

def wrong_append(a, b, e):
  match a:
    case []:
      e
    case +h <> +t:
      step_true(DP.note.wrong(h), _u => DP.wrong(List.append(&2, DP.Note, t, b)),
        wrong_append(t, b, e))

# LAW: one step of the front, with its head decided
law wrong_left.step:
  for bb: Bool
  for +t: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for e: {DP.has.step(bb, _u => DP.wrong(t)) == True{} : Bool}
  for ih: {DP.wrong(t) == True{} : Bool}
    -> {DP.wrong(List.append(&2, DP.Note, t, b)) == True{} : Bool}
  {DP.has.step(bb, _u => DP.wrong(List.append(&2, DP.Note, t, b))) == True{} : Bool}

def wrong_left.step(bb, _t, _b, e, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: and one with a problem in its front has one
law wrong_append_left:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for e: {DP.wrong(a) == True{} : Bool}
  {DP.wrong(List.append(&2, DP.Note, a, b)) == True{} : Bool}

def wrong_append_left(a, b, e):
  match a:
    case []:
      Eq.bit.absurd(&2, {DP.wrong(List.append(&2, DP.Note, [], b)) == True{} : Bool}, e)
    case h <> +t:
      wrong_left.step(DP.note.wrong(h), t, b, e, z => wrong_append_left(t, b, z))

# LAW: a plan over lines with a problem fails the command
law refuses_wrong:
  for +ns: List<&2, DP.Note>
  for e: {DP.wrong(ns) == True{} : Bool}
  {DP.refuses.plan(DP.plan.notes(ns)) == True{} : Bool}

def refuses_wrong(ns, e):
  %Equal.sym(Bool, DP.wrong(ns), True{}, e)
    : {DP.refuses.plan(P.Plan{DP.says(ns), DP.outcome.of(_)}) == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# a ledger that is not there, or not read

# LAW: doctor fails on a ledger it could not read, whatever else it found
law bad_fails:
  for +why: String
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  {DP.refuses.plan(DP.plan.of(M.Bad{why}, cc, lib, lock, rs, cs)) == True{} : Bool}

def bad_fails(why, cc, lib, lock, rs, cs):
  refuses_wrong(DP.notes.of(M.Bad{why}, DW.heard(rs, DW.Sources{}), cc, lib, lock, rs, cs),
    wrong_append_left(DP.head.notes(M.Bad{why}, cc, lib, lock, rs, cs),
      DP.imports.notes(M.Bad{why}, DW.heard(rs, DW.Sources{})),
      wrong_append(DP.probes(DP.programs(cc), rs),
        List.append(&2, DP.Note,
          [DP.ledger.note(M.Bad{why}), DP.lock.note(0n, DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
        wrong_append_left(
          [DP.ledger.note(M.Bad{why}), DP.lock.note(0n, DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
          {==}))))

# A NAR hash that is not empty takes the second arm, and one compared with
# itself is the arm that passes.
def L2.nar_why_agrees(n, url, rev, f):
  %f : {L.nar.why.go(_, String.eq(n, n), n, n, url, rev) == "" : String}
  Equal.cong(Bool, String, b => L.nar.why.go(False{}, b, n, n, url, rev),
    String.eq(n, n), True{}, Eq.string_eq_self(n))

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
  for +e: {D2.slashless(s) == True{} : Bool}
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
            Eq.and.left(Bool.not(Char.is_eq(h, '/')), D2.slashless(t), e))),
        spec_split(t, r,
          Eq.and.right(Bool.not(Char.is_eq(h, '/')), D2.slashless(t), e)))

def L8.spec_hash(h, rest, e):
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
        case W.Named{_names}:
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

# LAW: a names file laid leaves every path as it was: it is written under
# BEND_LIB, which is no path of the project
law names_put:
  for ns: List<&2, L.Name>
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.names.lay(ns, rest), p) == P.put.in(rest, p) : P.Wrote}

def names_put(ns, rest, p):
  match ns:
    case []:
      {==}
    case L.Name{_nv, _hash} <> t:
      names_put(t, rest, p)

# LAW: and so do the trees a lock lays with the names files after them
law lays_names_put:
  for +cs: List<&2, String>
  for +vs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +ns: List<&2, L.Name>
  for +rest: List<&2, P.Effect>
  for +p: String
  {P.put.in(P.lays(cs, vs, js, P.names.lay(ns, rest)), p) == P.put.in(rest, p) : P.Wrote}

def lays_names_put(cs, vs, js, ns, rest, p):
  Equal.trans(P.Wrote, P.put.in(P.lays(cs, vs, js, P.names.lay(ns, rest)), p),
    P.put.in(P.names.lay(ns, rest), p), P.put.in(rest, p),
    lays_put(cs, vs, js, P.names.lay(ns, rest), p), names_put(ns, rest, p))

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
  {P.put.plan(P.made(nx, cs, js, d), "ez.lock.toml") == D1.put.doc(d) : P.Wrote}

def made_put(nx, cs, js, d):
  match d:
    case P.Doc{+text}:
      Equal.trans(P.Wrote,
        P.put.in(P.says.of(Up.next.says(nx),
          P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(text),
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}])))))),
          "ez.lock.toml"),
        P.put.in(P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(text),
          P.edits.of(Up.next.edits(nx),
            P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))))),
          "ez.lock.toml"),
        P.Put{text},
        says_put(Up.next.says(nx),
          P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(text),
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))))),
          "ez.lock.toml"),
        Equal.trans(P.Wrote,
          P.put.in(P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(text),
            P.edits.of(Up.next.edits(nx),
              P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))))),
            "ez.lock.toml"),
          P.put.in(P.edits.of(Up.next.edits(nx),
            P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), text}]))),
            "ez.lock.toml"),
          P.Put{text},
          lays_names_put(cs, Up.next.vends(nx), js, L.names.read(text),
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

# LAW: what `ez lock` writes to its lock is a function of what the planner
# decided over the World's Inputs
law put_decides:
  for w: W.World
  {P.put(w, "ez.lock.toml") == D1.put.doc(P.decide(W.inputs(w))) : P.Wrote}

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

def L1.lock_reproducible(w1, w2, e):
  Equal.trans(P.Wrote,
    P.put(w1, "ez.lock.toml"),
    D1.put.doc(P.decide(W.inputs(w1))),
    P.put(w2, "ez.lock.toml"),
    put_decides(w1),
    Equal.trans(P.Wrote,
      D1.put.doc(P.decide(W.inputs(w1))),
      D1.put.doc(P.decide(W.inputs(w2))),
      P.put(w2, "ez.lock.toml"),
      Equal.cong(W.Inputs, P.Wrote, ins => D1.put.doc(P.decide(ins)),
        W.inputs(w1), W.inputs(w2), e),
      Equal.sym(P.Wrote, P.put(w2, "ez.lock.toml"),
        D1.put.doc(P.decide(W.inputs(w2))), put_decides(w2))))

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
    case L.Member{path, entry}:
      {==}

# membership

# LAW: an `any` whose rest answers True answers True
law any_true:
  for bb: Bool
  for rest: Unit -> Bool
  for e: {rest(Unit{}) == True{} : Bool}
  {L.any.step(bb, rest) == True{} : Bool}

def any_true(bb, _rest, e):
  match bb:
    case True{}:
      {==}
    case False{}:
      e

# LAW: a list holds what its tail holds, with anything before it
law holds_right:
  for p: List<&2, String>
  for +q: List<&2, String>
  for +x: String
  for e: {L.seen.holds(q, x) == True{} : Bool}
  {L.seen.holds(List.append(&2, String, p, q), x) == True{} : Bool}

def holds_right(p, q, x, e):
  match p:
    case []:
      e
    case +y <> +t:
      any_true(String.eq(y, x), _u => L.seen.holds(List.append(&2, String, t, q), x),
        holds_right(t, q, x, e))

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

# a dependency kept as it is, with the lines it says
def kept(d: M.Dep, s: List<&2, String>) -> Up.Fate:
  Up.Became{d, "", "", "", False{}, s, []}

# a fate with the pin it left kept, saying the lines given
def still(f: Up.Fate, s: List<&2, String>) -> Up.Fate:
  match f:
    case Up.Became{d, _o, _n, _p, _m, _s, _t}:
      kept(d, s)
    case Up.Waits{+a}:
      Up.Waits{a}
    case Up.Halts{+w}:
      Up.Halts{w}

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

# the hashes a ledger model vendors
def vends.of(model: M.Read) -> List<&2, String>:
  match model:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _hpa, _hpv, ds, _ts} = m
      I.vended(ds)

# the `.gitignore` an upgrade of a ledger model writes, given the one it reads
def gi.of(model: M.Read, +g: String) -> List<&2, Up.Edit>:
  match model:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _hpa, _hpv, +ds, _ts} = m
      +allow = I.sync(ds, g)
      Up.edit.if(String.eq(allow, g), ".gitignore", allow, [])

# what an upgrade of a ledger model decides when every pin is at its tip:
# the model as it is, nothing refused, asked, checked out, moved or removed,
# and at most `.gitignore` written
def target(+model: M.Read, +g: String) -> Up.Next:
  Up.Next{model, model, "", [], [], vends.of(model), [], gi.of(model, g), [], [], []}

# ---------------------------------------------------------------------------
# a plain lock writes only the lock (laws/WorkspaceLocksOnce.bend)

# and a plain lock leaves every path but the lock's as it was, whatever was
# decided: the one file it writes is the lock
def made_keeps_other(
  _led: M.Read,
  +cs: List<&2, String>,
  +js: List<&2, W.Judged>,
  d: P.Doc,
  +path: String,
  ep: {String.eq(P.lockfile(), path) == False{} : Bool}
) -> {P.put.plan(P.made(Up.plain(_led), cs, js, d), path) == P.Kept{} : P.Wrote}:
  match d:
    case P.Doc{+text}:
      Equal.trans(P.Wrote,
        P.put.in(P.lays(cs, [], js, P.names.lay(L.names.read(text), [P.Write{P.lockfile(), text}])), path),
        P.put.in([P.Write{P.lockfile(), text}], path),
        P.Kept{},
        lays_names_put(cs, [], js, L.names.read(text), [P.Write{P.lockfile(), text}], path),
        Equal.cong(Bool, P.Wrote, bb => Bool.pick(P.Wrote, bb, P.Put{text}, P.Kept{}),
          String.eq(P.lockfile(), path), False{}, ep))
    case P.Stop{_why}:
      {==}

def L3.plain_lock_writes_only_lock(w, e, path, ep):
  match w:
    case W.World{args, +ledger, listing, +replies, ups}:
      match args:
        case W.Args{up, only, here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.put(W.World{W.Args{True{}, only, here}, ledger, listing,
                replies, ups}, path) == P.Kept{} : P.Wrote}, e)
            case False{}:
              made_keeps_other(W.parsed(ledger),
                P.cloned(W.replies.of(Up.plain(W.parsed(ledger)), replies)),
                W.judged.of(Up.plain(W.parsed(ledger)), replies),
                P.decide(W.Inputs{W.parsed(ledger), "", listing,
                  W.judged.of(Up.plain(W.parsed(ledger)), replies)}), path, ep)

def wr(k: K.Walked) -> String:
  match k:
    case K.Walked{_h, r, _fs, _ss}:
      r
    case K.Asks{_at}:
      ""
    case K.Refused{_why}:
      ""

def ws(k: K.Walked) -> List<&2, K.Item>:
  match k:
    case K.Walked{_h, _r, _fs, ss}:
      ss
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

def aa(+w: A.World) -> String:
  AP.at.of(wr(AP.walked(w)), w)

# LAW: both halves of an `and` that are True
law both:
  for x: Bool
  for y: Bool
  for ex: {x == True{} : Bool}
  for ey: {y == True{} : Bool}
  {Bool.and(x, y) == True{} : Bool}

def both(x, y, ex, ey):
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

# LAW: a write to another path leaves what the rest of the plan left at this
# one
law one_passes:
  for +pw: String
  for +t: String
  for +path: String
  for +w: P.Wrote
  for ne: {String.eq(pw, path) == False{} : Bool}
  {P.put.one(P.Write{pw, t}, path, w) == w : P.Wrote}

def one_passes(pw, t, path, w, ne):
  match w:
    case P.Kept{}:
      %Equal.sym(Bool, String.eq(pw, path), False{}, ne)
        : {Bool.pick(P.Wrote, _, P.Put{t}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}
    case P.Put{_l}:
      {==}

# LAW: the ignore rules, written or not, leave every other path to the rest
law ignore_passes:
  for +ms: List<&2, String>
  for +text: String
  for +rest: List<&2, P.Effect>
  for +path: String
  for ne: {String.eq(".gitignore", path) == False{} : Bool}
  {P.put.in(IP.ignore.put(ms, text, rest), path) == P.put.in(rest, path) : P.Wrote}

def ignore_passes(ms, text, rest, path, ne):
  match ms:
    case []:
      {==}
    case h <> t:
      one_passes(".gitignore", IP.ignored(text, h <> t), path, P.put.in(rest, path), ne)

# LAW: removing committed trees writes nothing at any path
law drops_keep_remove:
  for hs: List<&2, String>
  for +path: String
  {P.put.in(P.drops.of(hs, []), path) == P.Kept{} : P.Wrote}

def drops_keep_remove(hs, path):
  match hs:
    case []:
      {==}
    case _h <> t:
      drops_keep_remove(t, path)

# LAW: nor does the `.gitignore` write, at ez.toml
law ignore_keeps_ledger_remove:
  for b: Bool
  for +next: String
  for hs: List<&2, String>
  {P.put.in(RP.ignore.put(b, next, P.drops.of(hs, [])), "ez.toml") == P.Kept{}
    : P.Wrote}

def ignore_keeps_ledger_remove(b, next, hs):
  match b:
    case True{}:
      drops_keep_remove(hs, "ez.toml")
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(hs, []), "ez.toml"), P.Kept{},
        drops_keep_remove(hs, "ez.toml"))
        : {P.put.one(P.Write{".gitignore", next}, "ez.toml", _) == P.Kept{} : P.Wrote}
      {==}

# LAW: a plan over a ledger that names the dependency writes the edited
# ledger to ez.toml; the arm that does not name it refuses, against the
# premise
law edits_has:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for ok: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == False{} : Bool}
  {P.put.plan(RP.plan.has(h, m, name, ignore), "ez.toml")
    == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}

def edits_has(h, m, name, ignore, ok):
  match h:
    case True{}:
      %Equal.sym(P.Wrote,
        P.put.in(RP.ignore.put(
          String.eq(I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore),
          I.sync(RP.deps.of(Rend.remove(m, name)), ignore),
          P.drops.of(RP.gone(RP.deps.of(m), name, RP.deps.of(Rend.remove(m, name))), [])),
          "ez.toml"),
        P.Kept{},
        ignore_keeps_ledger_remove(
          String.eq(I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore),
          I.sync(RP.deps.of(Rend.remove(m, name)), ignore),
          RP.gone(RP.deps.of(m), name, RP.deps.of(Rend.remove(m, name)))))
        : {P.put.one(P.Write{"ez.toml", Rend.show(Rend.remove(m, name))}, "ez.toml", _)
          == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}
      {==}
    case False{}:
      Eq.bit.absurd2(&2, {P.put.plan(RP.plan.has(False{}, m, name, ignore), "ez.toml")
        == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}, ok)

# The read is rewritten to the ledger in the goal, and in the premise by the
# same equation carried through `refuses.plan`.
def L6.remove_edits_ledger(name, s, ignore, m, good, ok):
  %good : {P.put.plan(RP.plan.read(_, name, ignore), "ez.toml")
    == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}
  edits_has(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))), m, name, ignore,
    Equal.trans(Bool,
      RP.refuses.plan(RP.plan.read(M.Good{m}, name, ignore)),
      RP.refuses.plan(RP.plan.read(M.parse(s), name, ignore)),
      False{},
      Equal.cong(M.Read, Bool, x => RP.refuses.plan(RP.plan.read(x, name, ignore)),
        M.Good{m}, M.parse(s), good),
      ok))

# what is left of a join once its hub is taken off
def join.rest(
  +root: M.Manifest,
  +ms: List<&2, J.Member>,
  +ev: {J.ok(root, ms) == True{} : Bool}
) -> {Bool.and(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
    J.tools.agree(J.all.tools(root, ms))) == True{} : Bool}:
  Eq.and.right(J.hubs(J.root.hub(root), ms),
    Bool.and(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
      J.tools.agree(J.all.tools(root, ms))), ev)

# and its dependencies' half
def join.deps(
  +root: M.Manifest,
  +ms: List<&2, J.Member>,
  +ev: {J.ok(root, ms) == True{} : Bool}
) -> {Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))) == True{} : Bool}:
  Eq.and.left(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
    J.tools.agree(J.all.tools(root, ms)), join.rest(root, ms, ev))

# target: each law's word is built from literal chars around the parts that
# are left open, so the chars that decide it compute. What does not compute is
# a fact about an open part, and each of those is a lemma below.

# LAW: a word with a char in front of anything is not empty
law nonempty_app:
  for a: String
  for c: Char
  for t: String
  {False{} == String.is_empty(a ++ SCon{c, t}) : Bool}

def nonempty_app(a, _c, _t):
  match a:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

# LAW: one char of a search for `://`, with whether the pattern starts there
# given as a parameter
law contains_url.arm:
  for +t: String
  for s: Bool
  for ih: {String.contains(t, "://") == True{} : Bool}
  {String.contains.if(t, "://", s) == True{} : Bool}

def contains_url.arm(_t, s, ih):
  match s:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: `://` is found wherever it is put
law contains_url:
  for +a: String
  for +b: String
  {String.contains(a ++ ("://" ++ b), "://") == True{} : Bool}

def contains_url(a, b):
  match a:
    case SNil{}:
      %Equal.sym(Bool, String.starts_with(b, ""), True{}, Eq.starts_nil(b)) :
        {String.contains.if("//" ++ b, "://", _) == True{} : Bool}
      {==}
    case SCon{+h, +t}:
      contains_url.arm(t ++ ("://" ++ b),
        String.starts_with(SCon{h, t ++ ("://" ++ b)}, "://"),
        contains_url(t, b))

# LAW: the ledger's name for a git source it holds first is that name
law had_first:
  for n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for fresh: String
  {Named.had(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    fresh) == n : String}

def had_first(n, _h, _en, url, _rev, _tag, _root, _nar, _vend, t, fresh):
  %Equal.sym(Bool, String.eq(url, url), True{}, Eq.string_eq_self(url)) :
    {Named.had.at(_, n, Named.had(t, url, fresh)) == n : String}
  {==}

# LAW: a record with no commit reuses nothing, whatever is on record
law no_rev:
  for was: KKey.Stamp
  for +f: String
  for +b: String
  {KKey.reuse(was, KKey.Stamp{"", f, b}) == False{} : Bool}

def no_rev(was, _f, _b):
  match was:
    case KKey.Stamp{_r0, _f0, _b0}:
      {==}
