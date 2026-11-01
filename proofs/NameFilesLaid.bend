# proofs of laws/NameFilesLaid.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/git/git.bend as Git
import ../src/lock/lock.bend as L
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/add/world.bend as A
import ../src/add/hub.bend as H
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/NameFilesLaid.bend as Laws
import ../laws/defs/NamesLaid.bend as D1
import ../laws/defs/NamesLaidByParts.bend as D2
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

# ---------------------------------------------------------------------------
# names files

# LAW: the library's line is a problem when one of its checks failed,
# whatever the other said
law lib_said_bad:
  for a: Bool
  for +dir: String
  for +count: Nat
  for +names: Nat
  for gone: List<&2, String>
  for bad: List<&2, String>
  {DP.note.wrong(DP.lib.said(Bool.and(a, False{}), dir, count, names, gone, bad)) == True{} : Bool}

def lib_said_bad(a, _dir, _count, _names, _gone, _bad):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: and a name whose file is wrong makes it one
law lib_names_bad:
  for +dir: String
  for +want: List<&2, String>
  for +ns: List<&2, L.Name>
  for +have: List<&2, String>
  for +rs: List<&2, DW.Reply>
  for +x: String
  for +xs: List<&2, String>
  for b: {x <> xs == DP.names.wrong(ns, rs) : List<&2, String>}
  {DP.note.wrong(DP.lib.judge(dir, want, ns, have, rs)) == True{} : Bool}

def lib_names_bad(dir, want, ns, have, _rs, x, xs, b):
  %b : {DP.note.wrong(DP.lib.said(
    Bool.and(List.is_empty(&2, String, DP.missing(want, have)), List.is_empty(&2, String, _)),
    dir, List.length(&2, String, want), List.length(&2, L.Name, ns), DP.missing(want, have), _))
    == True{} : Bool}
  lib_said_bad(List.is_empty(&2, String, DP.missing(want, have)), dir,
    List.length(&2, String, want), List.length(&2, L.Name, ns), DP.missing(want, have), x <> xs)

# LAW: three lines whose last is a problem have one
law wrong_third:
  for +n1: DP.Note
  for +n2: DP.Note
  for +n3: DP.Note
  for e: {DP.note.wrong(n3) == True{} : Bool}
  {DP.wrong([n1, n2, n3]) == True{} : Bool}

def wrong_third(n1, n2, n3, e):
  M2.step_true(DP.note.wrong(n1), _u => DP.wrong([n2, n3]),
    M2.step_true(DP.note.wrong(n2), _u => DP.wrong([n3]),
      M2.step_hit(DP.note.wrong(n3), _u => DP.wrong([]), e)))

# LAW: a library line that is a problem fails doctor
law wrong_lib:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for +x: String
  for +xs: List<&2, String>
  for b: {x <> xs == DP.names.wrong(DP.lock.names(lock), rs) : List<&2, String>}
  {DP.refuses.plan(DP.plan.notes(DP.notes.of(led, got, cc, lib, lock, rs, cs))) == True{} : Bool}

def wrong_lib(led, got, cc, lib, lock, rs, cs, x, xs, b):
  M2.refuses_wrong(DP.notes.of(led, got, cc, lib, lock, rs, cs),
    M2.wrong_append_left(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got),
      M2.wrong_append(DP.probes(DP.programs(cc), rs),
        List.append(&2, DP.Note,
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
        M2.wrong_append_left(
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
          wrong_third(DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs),
            lib_names_bad(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock),
              DP.lib.have(DW.heard(rs, DW.Lib{DP.lib.at(lib)})), rs, x, xs, b))))))

def Laws.doctor_wrong_name_fails(w, x, xs, b):
  wrong_lib(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), x, xs, b)

# LAW: the lines a hub add tells lay no name's file
law hsays_unnamed:
  for c: Bool
  for +w: A.World
  for +h: String
  for +e: String
  {H.names.laid(Bool.pick(List<&2, P.Effect>, c, [P.Say{A.target(w) ++ " is " ++ h}],
    [P.Say{A.target(w) ++ " is " ++ h}, P.Say{Git.import.line(A.target(w), Path.norm(e))}]))
    == [] : List<&2, L.Name>}

def hsays_unnamed(c, _w, _h, _e):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: nothing after the ledger's write lays a name's file
law hignore_unnamed:
  for b: Bool
  for +next: String
  for +h: String
  for +e: String
  for +w: A.World
  {H.names.laid(H.ignore.put(b, next, H.says(h, e, w))) == [] : List<&2, L.Name>}

def hignore_unnamed(b, _next, _h, e, _w):
  match b:
    case True{}:
      hsays_unnamed(String.is_empty(e), _w, _h, e)
    case False{}:
      hsays_unnamed(String.is_empty(e), _w, _h, e)

def Laws.add_named_lays_name(w, ok):
  %Equal.sym(P.Plan, H.plan(w), P.Plan{M1.heff(w), P.Success{}}, M1.hsucceeds(w, ok))
    : {H.names.laid(P.effects(_)) == [L.Name{A.target(w), M.dep.hash(H.added(w))}]
      : List<&2, L.Name>}
  Equal.cong(List<&2, L.Name>, List<&2, L.Name>,
    t => L.Name{A.target(w), M.dep.hash(H.added(w))} <> t,
    H.names.laid(H.ignore.put(M1.hsame(w), M1.hnext(w), H.says(H.hash(w), M.dep.entry(H.added(w)),
      w))), [],
    hignore_unnamed(M1.hsame(w), M1.hnext(w), H.hash(w), M.dep.entry(H.added(w)), w))

def Laws.fetch_lays_missing_name(rs, nv, hash, v, g):
  %v : {FP.name.valid(_, rs, nv, hash) == FP.NmPut{nv, hash, ""} : FP.Nm}
  %g : {FP.name.heard(_, nv, hash) == FP.NmPut{nv, hash, ""} : FP.Nm}
  {==}

def Laws.fetch_rewrites_name(rs, nv, hash, x, v, g, ne):
  %v : {FP.name.valid(_, rs, nv, hash) == FP.NmPut{nv, hash, String.trim(x)} : FP.Nm}
  %g : {FP.name.heard(_, nv, hash) == FP.NmPut{nv, hash, String.trim(x)} : FP.Nm}
  %ne : {FP.name.held(_, nv, hash, String.trim(x)) == FP.NmPut{nv, hash, String.trim(x)} : FP.Nm}
  {==}

def Laws.fetch_refuses_unread_name(rs, nv, hash, v):
  %v : {FP.names.outcome([FP.name.valid(_, rs, nv, hash)])
    == P.Refused{"ez: the lock names " ++ nv ++ " as " ++ hash ++
      ", which bend would not read back; run ez lock"} : P.Outcome}
  {==}

# LAW: one names file, said or not, lays its name
law nm.laid_put:
  for b: Bool
  for +nv: String
  for +hash: String
  for was: String
  for +rest: List<&2, P.Effect>
  {D1.names.laid(FP.name.put.at(b, nv, hash, was, rest))
    == L.Name{nv, hash} <> D1.names.laid(rest) : List<&2, L.Name>}

def nm.laid_put(b, _nv, _hash, _was, _rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the names files laid ahead of the trees are the names the parts lay
law nm.laid_names_fetch:
  for ms: List<&2, FP.Nm>
  for +rest: List<&2, P.Effect>
  {D1.names.laid(FP.names.lay(ms, rest))
    == List.append(&2, L.Name, D2.puts(ms), D1.names.laid(rest)) : List<&2, L.Name>}

def nm.laid_names_fetch(ms, rest):
  match ms:
    case []:
      {==}
    case m <> +t:
      match m:
        case FP.NmPut{+nv, +hash, +was}:
          Equal.trans(List<&2, L.Name>,
            D1.names.laid(FP.name.put.at(String.is_empty(was), nv, hash, was, FP.names.lay(t, rest))),
            L.Name{nv, hash} <> D1.names.laid(FP.names.lay(t, rest)),
            L.Name{nv, hash} <> List.append(&2, L.Name, D2.puts(t), D1.names.laid(rest)),
            nm.laid_put(String.is_empty(was), nv, hash, was, FP.names.lay(t, rest)),
            Equal.cong(List<&2, L.Name>, List<&2, L.Name>, r => L.Name{nv, hash} <> r,
              D1.names.laid(FP.names.lay(t, rest)),
              List.append(&2, L.Name, D2.puts(t), D1.names.laid(rest)), nm.laid_names_fetch(t, rest)))
        case FP.NmAsk{_nv}:
          nm.laid_names_fetch(t, rest)
        case FP.NmKeep{}:
          nm.laid_names_fetch(t, rest)
        case FP.NmStop{_why}:
          nm.laid_names_fetch(t, rest)

# LAW: the trees a fetch lays lay no names file
law nm.laid_trees:
  for vs: List<&2, FP.Verdict>
  {D1.names.laid(FP.effects.of(vs)) == [] : List<&2, L.Name>}

def nm.laid_trees(vs):
  match vs:
    case []:
      {==}
    case v <> +t:
      match v:
        case FP.Keep{}:
          nm.laid_trees(t)
        case FP.Put{_hash, _ls}:
          nm.laid_trees(t)
        case FP.Stop{_why}:
          nm.laid_trees(t)

# LAW: a sealed plan that does not refuse holds the effects it was given
law nm.seal_es:
  for +es: List<&2, P.Effect>
  for o: P.Outcome
  for ok: {FP.refuses.plan(FP.seal(es, o)) == False{} : Bool}
  {FP.effects(FP.seal(es, o)) == es : List<&2, P.Effect>}

def nm.seal_es(es, o, ok):
  match o:
    case P.Success{}:
      {==}
    case P.Refused{_why}:
      Eq.bit.absurd2(&2, {FP.effects(FP.seal(es, P.Refused{_why})) == es : List<&2, P.Effect>}, ok)

law nm.lays_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  for ok: {FP.refuses.plan(FP.plan.led(b, g, w)) == False{} : Bool}
  {D1.names.laid(FP.effects(FP.plan.led(b, g, w))) == D2.puts(FP.name.parts.of(F.sects(w), w))
    : List<&2, L.Name>}

def nm.lays_led(b, g, w, ok):
  match b:
    case False{}:
      Eq.bit.absurd2(&2, {D1.names.laid(FP.effects(FP.plan.led(False{}, g, w)))
        == D2.puts(FP.name.parts.of(F.sects(w), w)) : List<&2, L.Name>}, ok)
    case True{}:
      match g:
        case None{}:
          Eq.bit.absurd2(&2, {D1.names.laid(FP.effects(FP.plan.led(True{}, None{}, w)))
            == D2.puts(FP.name.parts.of(F.sects(w), w)) : List<&2, L.Name>}, ok)
        case Some{_t}:
          +ms = FP.name.parts.of(F.sects(w), w)
          +vs = FP.judged(FP.parts.of(F.sects(w), w))
          +es = FP.names.lay(ms, FP.effects.of(vs))
          +o = FP.outcome.then(FP.outcome.of(vs), FP.names.outcome(ms))
          Equal.trans(List<&2, L.Name>,
            D1.names.laid(FP.effects(FP.seal(es, o))), D1.names.laid(es), D2.puts(ms),
            Equal.cong(List<&2, P.Effect>, List<&2, L.Name>, x => D1.names.laid(x),
              FP.effects(FP.seal(es, o)), es, nm.seal_es(es, o, ok)),
            Equal.trans(List<&2, L.Name>,
              D1.names.laid(es), List.append(&2, L.Name, D2.puts(ms), D1.names.laid(FP.effects.of(vs))),
              D2.puts(ms),
              nm.laid_names_fetch(ms, FP.effects.of(vs)),
              Equal.trans(List<&2, L.Name>,
                List.append(&2, L.Name, D2.puts(ms), D1.names.laid(FP.effects.of(vs))),
                List.append(&2, L.Name, D2.puts(ms), []), D2.puts(ms),
                Equal.cong(List<&2, L.Name>, List<&2, L.Name>, x => List.append(&2, L.Name, D2.puts(ms), x),
                  D1.names.laid(FP.effects.of(vs)), [], nm.laid_trees(vs)),
                Str.list_append_nil(L.Name, D2.puts(ms)))))

def Laws.fetch_lays_the_names(w, ok):
  nm.lays_led(F.ledger(w), F.lock(w), w, ok)
