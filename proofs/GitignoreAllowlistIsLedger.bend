# proofs of laws/GitignoreAllowlistIsLedger.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/relock/relock.bend as R
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/ledger/ignore.bend as I
import ../src/pub/blurb.bend as B
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/remove/plan.bend as RP
import ../laws/GitignoreAllowlistIsLedger.bend as Laws
import ../laws/defs/LockInputs.bend as D1
import ../laws/defs/WorldAfterLock.bend as D2
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/AllowlistBlock.bend as M2
import ./lemmas/AllowlistLines.bend as M3
import ./lemmas/LockPlannerFacts.bend as M4
import ./lemmas/NewlineFreeLines.bend as M5
import ./lemmas/PlanEffectFacts.bend as M6
import ./lemmas/RenderedLedgerRows.bend as M7
import ./lemmas/UpgradeKeeps.bend as M8
import ./lemmas/UpgradeWritesAroundLedger.bend as M9

# LAW: and its right half
law or_right_ledger:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_right_ledger(a, b, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {b == False{} : Bool}, e)
    case False{}:
      e

# LAW: a list none of whose hashes `h <> seen` names has none `seen` names
law fresh_drop:
  for xs: List<&2, String>
  for +h: String
  for +seen: List<&2, String>
  for +e: {M6.fresh(xs, h <> seen) == True{} : Bool}
  {M6.fresh(xs, seen) == True{} : Bool}

def fresh_drop(xs, h, seen, e):
  match xs:
    case []:
      {==}
    case +x <> +r:
      M6.and_tt(Bool.not(I.named(seen, x)), M6.fresh(r, seen),
        M9.not_of_false(I.named(seen, x),
          or_right_ledger(String.eq(h, x), I.named(seen, x),
            Eq.not.true(Bool.or(String.eq(h, x), I.named(seen, x)),
              Eq.and.left(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
                M6.fresh(r, h <> seen), e)))),
        fresh_drop(r, h, seen,
          Eq.and.right(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
            M6.fresh(r, h <> seen), e)))

# LAW: and does not name `h`
law fresh_miss:
  for xs: List<&2, String>
  for +h: String
  for +seen: List<&2, String>
  for +e: {M6.fresh(xs, h <> seen) == True{} : Bool}
  {I.named(xs, h) == False{} : Bool}

def fresh_miss(xs, h, seen, e):
  match xs:
    case []:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, String.eq(x, h), False{},
        M9.eq_flip(h, x,
          M5.or_left_ledger(String.eq(h, x), I.named(seen, x),
            Eq.not.true(Bool.or(String.eq(h, x), I.named(seen, x)),
              Eq.and.left(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
                M6.fresh(r, h <> seen), e)))))
        : {Bool.or(_, I.named(r, h)) == False{} : Bool}
      fresh_miss(r, h, seen,
        Eq.and.right(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
          M6.fresh(r, h <> seen), e))

# LAW: one hash of the walk, with whether it is passed over given as a
# parameter: what it keeps is none of what it has seen
law fresh_once.arm:
  for +h: String
  for +t: List<&2, String>
  for +seen: List<&2, String>
  for skip: Bool
  for es: {Bool.or(String.is_empty(h), I.named(seen, h)) == skip : Bool}
  for ih: {M6.fresh(I.once.go(t, I.once.seen(skip, h, seen)), I.once.seen(skip, h, seen))
    == True{} : Bool}
  {M6.fresh(I.once.put(skip, h, I.once.go(t, I.once.seen(skip, h, seen))), seen)
    == True{} : Bool}

def fresh_once.arm(h, t, seen, skip, es, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      M6.and_tt(Bool.not(I.named(seen, h)), M6.fresh(I.once.go(t, h <> seen), seen),
        M9.not_of_false(I.named(seen, h),
          or_right_ledger(String.is_empty(h), I.named(seen, h), es)),
        fresh_drop(I.once.go(t, h <> seen), h, seen, ih))

# LAW: nothing the walk keeps is a hash it was told it had seen
law fresh_once:
  for hs: List<&2, String>
  for +seen: List<&2, String>
  {M6.fresh(I.once.go(hs, seen), seen) == True{} : Bool}

def fresh_once(hs, seen):
  match hs:
    case []:
      {==}
    case +h <> +t:
      fresh_once.arm(h, t, seen, Bool.or(String.is_empty(h), I.named(seen, h)), {==},
        fresh_once(t, I.once.seen(Bool.or(String.is_empty(h), I.named(seen, h)), h, seen)))

# LAW: one hash of the walk, with whether it is passed over given as a
# parameter: a kept hash is none of the hashes kept after it
law once_distinct.arm:
  for +h: String
  for +t: List<&2, String>
  for +seen: List<&2, String>
  for skip: Bool
  for ih: {Laws.hashes.distinct(I.once.go(t, I.once.seen(skip, h, seen))) == True{} : Bool}
  {Laws.hashes.distinct(I.once.put(skip, h, I.once.go(t, I.once.seen(skip, h, seen))))
    == True{} : Bool}

def once_distinct.arm(h, t, seen, skip, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      M6.and_tt(Bool.not(I.named(I.once.go(t, h <> seen), h)),
        Laws.hashes.distinct(I.once.go(t, h <> seen)),
        M9.not_of_false(I.named(I.once.go(t, h <> seen), h),
          fresh_miss(I.once.go(t, h <> seen), h, seen, fresh_once(t, h <> seen))),
        ih)

# LAW: the walk keeps each hash once
law once_distinct:
  for hs: List<&2, String>
  for +seen: List<&2, String>
  {Laws.hashes.distinct(I.once.go(hs, seen)) == True{} : Bool}

def once_distinct(hs, seen):
  match hs:
    case []:
      {==}
    case +h <> +t:
      once_distinct.arm(h, t, seen, Bool.or(String.is_empty(h), I.named(seen, h)),
        once_distinct(t, I.once.seen(Bool.or(String.is_empty(h), I.named(seen, h)), h, seen)))

def Laws.vended_once(ds):
  once_distinct(I.vendors(ds), [])

# the text a path was written with, "" when it was not
def wrote.text_lock(w: P.Wrote) -> String:
  match w:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

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
  for h: M9.ok.go(a, b, t, vs, model, ig)
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
  for h: M9.ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {Bool.pick(P.Wrote, c, P.Put{t2}, P.Kept{}) == P.Put{t} : P.Wrote}
  for +ev: {Str.clear.all(vs, '\n') == True{} : Bool}
  {I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
    {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}

def ign_kept(c, q, t2, t, ec, vs, model, ig, h, e, ev):
  match c:
    case False{}:
      Empty.absurd({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
        {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>},
        M8.kept_put_lock(t, e))
    case True{}:
      %Equal.cong(P.Wrote, String, x => wrote.text_lock(x), P.Put{t2}, P.Put{t}, e)
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
  for h: M9.ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
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
  for h: M9.ok.edits(es, vs, model, ig)
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
        M8.kept_put_lock(t, Equal.trans(P.Wrote, P.Kept{}, P.put.in(rest, ".gitignore"), P.Put{t},
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
  for h: M9.ok.go(a, b, t, vs, model, ig)
  {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}

def ok_go_toml(a, b, _t, vs, model, _ig, ea, h):
  match a b:
    case True{} _:
      h
    case False{} True{}:
      Eq.bit.absurd(&2, {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}, ea)
    case False{} False{}:
      Eq.bit.absurd(&2, {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}, ea)

law toml_kept:
  for c: Bool
  for +q: String
  for +t2: String
  for +t: String
  for +ec: {String.eq(q, "ez.toml") == c : Bool}
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: M9.ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {Bool.pick(P.Wrote, c, P.Put{t2}, P.Kept{}) == P.Put{t} : P.Wrote}
  {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}

def toml_kept(c, q, t2, t, ec, vs, model, ig, h, e):
  match c:
    case False{}:
      Empty.absurd({vs == I.vended(D1.ledger.deps(model)) : List<&2, String>},
        M8.kept_put_lock(t, e))
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
  for h: M9.ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t2, vs, model, ig)
  for e: {P.put.one(P.Write{q, t2}, "ez.toml", r) == P.Put{t} : P.Wrote}
  for ih: {rr == P.Put{t} : P.Wrote} ->
    {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}
  {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}

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
  for h: M9.ok.edits(es, vs, model, ig)
  for +rest: List<&2, P.Effect>
  for +kr: {P.put.in(rest, "ez.toml") == P.Kept{} : P.Wrote}
  for +t: String
  for e: {P.put.in(P.edits.of(es, rest), "ez.toml") == P.Put{t} : P.Wrote}
  {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}

def edits_toml(es, vs, model, ig, h, rest, kr, t, e):
  match es:
    case []:
      Empty.absurd({vs == I.vended(D1.ledger.deps(model)) : List<&2, String>},
        M8.kept_put_lock(t, Equal.trans(P.Wrote, P.Kept{}, P.put.in(rest, "ez.toml"), P.Put{t},
          Equal.sym(P.Wrote, P.put.in(rest, "ez.toml"), P.Kept{}, kr), e)))
    case Up.Edit{+q, +t2} <> +tl:
      (h1, h2) = h
      toml_arm(P.put.in(P.edits.of(tl, rest), "ez.toml"), q, t2,
        P.put.in(P.edits.of(tl, rest), "ez.toml"), {==}, t, vs, model, ig, h1, e,
        x => edits_toml(tl, vs, model, ig, h2, rest, kr, t, x))

# LAW: a made plan's writes after the upgrade's own files, the sources and
# the lock, leave `.gitignore` and ez.toml as they were, when no source is at
# either
law rest_kept_lock:
  for +nx: Up.Next
  for +lt: String
  for +p: String
  for m: {D2.found.miss(Up.next.found(nx), p) == True{} : Bool}
  for lk: {P.put.in([P.Write{P.lockfile(), lt}], p) == P.Kept{} : P.Wrote}
  {P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), p) == P.Kept{} : P.Wrote}

def rest_kept_lock(nx, lt, p, m, lk):
  Equal.trans(P.Wrote,
    P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), p),
    P.put.in(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), p),
    P.Kept{},
    M9.src_miss(Up.next.found(nx), Up.next.swaps(nx),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), p, m),
    Equal.trans(P.Wrote,
      P.put.in(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), p),
      P.put.in([P.Write{P.lockfile(), lt}], p),
      P.Kept{},
      M6.drops_put(Up.next.drops(nx), [P.Write{P.lockfile(), lt}], p),
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
    P.put.in(P.says.of(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))))), p),
    P.put.in(P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), p),
    P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
      Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), p),
    M6.says_put(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), p),
    M6.lays_names_put(cs, Up.next.vends(nx), js, L.names.read(lt),
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
  for +miss: {D2.found.miss(Up.next.found(nx), ".gitignore") == True{} : Bool}
  for +ig: String
  for okn: M9.ok.next(nx, ig)
  for +ev: {Str.clear.all(Up.next.vends(nx), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(t)) == Up.next.vends(nx) : List<&2, String>} &
    {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>}

def ign_plan(d, nx, cs, js, t, e, miss, ig, okn, ev):
  match d:
    case P.Stop{_why}:
      Empty.absurd({I.hashes(I.file.lines(t)) == Up.next.vends(nx) : List<&2, String>} &
        {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>},
        M8.kept_put_lock(t, e))
    case P.Doc{+lt}:
      edits_ign(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig, okn,
        P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
          P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])),
        rest_kept_lock(nx, lt, ".gitignore", miss, {==}), t,
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
  for +miss: {D2.found.miss(D1.found(w), ".gitignore") == True{} : Bool}
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
        text, put, miss, D2.ignore.said(Up.text.said(ups, Up.Ignore{})),
        M9.ok_world(args, ledger, ups), ev)

# the first of two facts
def fst(-A: Type, -M7.B: Type, p: A & M7.B) -> A:
  (a, _b) = p
  a

# the second
def snd(-A: Type, -M7.B: Type, p: A & M7.B) -> M7.B:
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
  for +miss: {D2.found.miss(Up.next.found(nx), "ez.toml") == True{} : Bool}
  for +ig: String
  for okn: M9.ok.next(nx, ig)
  {Up.next.vends(nx) == I.vended(D1.ledger.deps(Up.next.model(nx))) : List<&2, String>}

def toml_plan(d, nx, cs, js, t, e, miss, ig, okn):
  match d:
    case P.Stop{_why}:
      Empty.absurd({Up.next.vends(nx) == I.vended(D1.ledger.deps(Up.next.model(nx)))
        : List<&2, String>}, M8.kept_put_lock(t, e))
    case P.Doc{+lt}:
      edits_toml(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig, okn,
        P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
          P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])),
        rest_kept_lock(nx, lt, "ez.toml", miss, {==}), t,
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
        text, put, miss, D2.ignore.said(Up.text.said(ups, Up.Ignore{})),
        M9.ok_world(args, ledger, ups))

# LAW: a lock that does not refuse read a ledger that parsed, once the
# upgrade did not stop
law rf.read:
  for read: M.Read
  for li: W.Listing
  for +js: List<&2, W.Judged>
  for ok: {P.refuses.doc(P.decide(W.Inputs{read, "", li, js})) == False{} : Bool}
  {D1.ledger.good(read) == True{} : Bool}

def rf.read(read, _li, _js, ok):
  match read:
    case M.Bad{_why}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, ok)
    case M.Good{_m}:
      {==}

# LAW: and it did not stop
law rf.stop:
  for stop: String
  for +read: M.Read
  for li: W.Listing
  for +js: List<&2, W.Judged>
  for ok: {P.refuses.doc(P.decide(W.Inputs{read, stop, li, js})) == False{} : Bool}
  {D1.ledger.good(read) == True{} : Bool}

def rf.stop(stop, read, li, js, ok):
  match stop:
    case SNil{}:
      rf.read(read, li, js, ok)
    case SCon{_c, _cs}:
      Eq.bit.absurd2(&2, {D1.ledger.good(read) == True{} : Bool}, ok)

# LAW: so a lock that does not refuse read a ledger that parsed
law rf.good:
  for +nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for ok: {P.refuses.doc(P.decide(W.inputs.of(nx, listing, replies))) == False{} : Bool}
  {D1.ledger.good(Up.next.read(nx)) == True{} : Bool}

def rf.good(nx, listing, replies, ok):
  rf.stop(Up.next.stop(nx), Up.next.read(nx), W.listing.of(nx, listing),
    W.judged.of(nx, replies), ok)

# the upgrade's own files' half of what a decision keeps
law kp.ven.of:
  for +nx: Up.Next
  for +old: M.Read
  for +ig: String
  for +R: List<&2, P.Effect>
  for k: M8.kp.next(nx, old, ig, R)
  for se: {String.is_empty(Up.next.stop(nx)) == True{} : Bool}
  for sg: {D1.ledger.good(Up.next.read(nx)) == True{} : Bool}
  M8.kp.ven(Up.next.edits(nx), Up.next.vends(nx), old, ig, R)

def kp.ven.of(_nx, _old, _ig, _R, k, se, sg):
  (_u, v) = k
  v(se)(sg)

# LAW: what the upgrade's own files say of `.gitignore` left unwritten
law kp.gi.go:
  for +edits: List<&2, Up.Edit>
  for +vends: List<&2, String>
  for +old: M.Read
  for +ig: String
  for +R: List<&2, P.Effect>
  for p: M8.kp.ven(edits, vends, old, ig, R)
  for k: {P.put.in(P.edits.of(edits, R), ".gitignore") == P.Kept{} : P.Wrote}
  for ev: {Str.clear.all(vends, '\n') == True{} : Bool}
  {I.hashes(I.file.lines(ig)) == vends : List<&2, String>}

def kp.gi.go(_edits, _vends, _old, _ig, _R, p, k, ev):
  (g, _t) = p
  g(k)(ev)

# LAW: and of ez.toml left unwritten
law kp.toml.go:
  for +edits: List<&2, Up.Edit>
  for +vends: List<&2, String>
  for +old: M.Read
  for +ig: String
  for +R: List<&2, P.Effect>
  for p: M8.kp.ven(edits, vends, old, ig, R)
  for k: {P.put.in(P.edits.of(edits, R), "ez.toml") == P.Kept{} : P.Wrote}
  {vends == I.vended(D1.ledger.deps(old)) : List<&2, String>}

def kp.toml.go(_edits, _vends, _old, _ig, _R, p, k):
  (_g, t) = p
  t(k)

# LAW: `.gitignore` left as it was by an upgrade whose lock did not refuse
law kp.gi.doc:
  for d: P.Doc
  for +only: String
  for +ledger: Maybe<&2, String>
  for +ups: List<&2, Up.Reply>
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for rd: {P.refuses.doc(d) == False{} : Bool}
  for e: {P.put.plan(P.made(Up.next(only, W.parsed(ledger), ups), cs, js, d), ".gitignore")
    == P.Kept{} : P.Wrote}
  for +se: {String.is_empty(Up.next.stop(Up.next(only, W.parsed(ledger), ups))) == True{} : Bool}
  for +sg: {D1.ledger.good(Up.next.read(Up.next(only, W.parsed(ledger), ups))) == True{} : Bool}
  for +ev: {Str.clear.all(Up.next.vends(Up.next(only, W.parsed(ledger), ups)), '\n') == True{}
    : Bool}
  {I.hashes(I.file.lines(D2.ignore.said(Up.text.said(ups, Up.Ignore{}))))
    == Up.next.vends(Up.next(only, W.parsed(ledger), ups)) : List<&2, String>}

def kp.gi.doc(d, only, ledger, ups, cs, js, rd, e, se, sg, ev):
  match d:
    case P.Stop{_why}:
      Eq.bit.absurd2(&2, {I.hashes(I.file.lines(D2.ignore.said(Up.text.said(ups, Up.Ignore{}))))
        == Up.next.vends(Up.next(only, W.parsed(ledger), ups)) : List<&2, String>}, rd)
    case P.Doc{+lt}:
      +nx = Up.next(only, W.parsed(ledger), ups)
      +ig = D2.ignore.said(Up.text.said(ups, Up.Ignore{}))
      +R = P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))
      kp.gi.go(Up.next.edits(nx), Up.next.vends(nx), W.parsed(ledger), ig, R,
        kp.ven.of(nx, W.parsed(ledger), ig, R, M8.kp_next(only, W.parsed(ledger), ups, R), se, sg),
        Equal.trans(P.Wrote, P.put.in(P.edits.of(Up.next.edits(nx), R), ".gitignore"),
          P.put.plan(P.made(nx, cs, js, P.Doc{lt}), ".gitignore"), P.Kept{},
          Equal.sym(P.Wrote, P.put.plan(P.made(nx, cs, js, P.Doc{lt}), ".gitignore"),
            P.put.in(P.edits.of(Up.next.edits(nx), R), ".gitignore"),
            made_edits(nx, cs, js, lt, ".gitignore")),
          e),
        ev)

# LAW: and ez.toml left as it was
law kp.toml.doc:
  for d: P.Doc
  for +only: String
  for +ledger: Maybe<&2, String>
  for +ups: List<&2, Up.Reply>
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for rd: {P.refuses.doc(d) == False{} : Bool}
  for e: {P.put.plan(P.made(Up.next(only, W.parsed(ledger), ups), cs, js, d), "ez.toml")
    == P.Kept{} : P.Wrote}
  for +se: {String.is_empty(Up.next.stop(Up.next(only, W.parsed(ledger), ups))) == True{} : Bool}
  for +sg: {D1.ledger.good(Up.next.read(Up.next(only, W.parsed(ledger), ups))) == True{} : Bool}
  {Up.next.vends(Up.next(only, W.parsed(ledger), ups))
    == I.vended(D1.ledger.deps(W.parsed(ledger))) : List<&2, String>}

def kp.toml.doc(d, only, ledger, ups, cs, js, rd, e, se, sg):
  match d:
    case P.Stop{_why}:
      Eq.bit.absurd2(&2, {Up.next.vends(Up.next(only, W.parsed(ledger), ups))
        == I.vended(D1.ledger.deps(W.parsed(ledger))) : List<&2, String>}, rd)
    case P.Doc{+lt}:
      +nx = Up.next(only, W.parsed(ledger), ups)
      +ig = D2.ignore.said(Up.text.said(ups, Up.Ignore{}))
      +R = P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))
      kp.toml.go(Up.next.edits(nx), Up.next.vends(nx), W.parsed(ledger), ig, R,
        kp.ven.of(nx, W.parsed(ledger), ig, R, M8.kp_next(only, W.parsed(ledger), ups, R), se, sg),
        Equal.trans(P.Wrote, P.put.in(P.edits.of(Up.next.edits(nx), R), "ez.toml"),
          P.put.plan(P.made(nx, cs, js, P.Doc{lt}), "ez.toml"), P.Kept{},
          Equal.sym(P.Wrote, P.put.plan(P.made(nx, cs, js, P.Doc{lt}), "ez.toml"),
            P.put.in(P.edits.of(Up.next.edits(nx), R), "ez.toml"),
            made_edits(nx, cs, js, lt, "ez.toml")),
          e))

def Laws.upgrade_allowlist_kept_in_sync(w, up, ok, kept, ev):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only, +here}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {I.hashes(I.file.lines(Laws.ignore.read(W.World{W.Args{False{}, only,
                here}, ledger, listing, replies, ups}))) == Laws.vends(W.World{W.Args{False{}, only,
                here}, ledger, listing, replies, ups}) : List<&2, String>}, up)
            case True{}:
              kp.gi.doc(P.decide(W.inputs.of(Up.next(only, W.parsed(ledger), ups), listing, replies)),
                only, ledger, ups, P.cloned(W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)),
                W.judged.of(Up.next(only, W.parsed(ledger), ups), replies), ok, kept,
                M6.mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok),
                rf.good(Up.next(only, W.parsed(ledger), ups), listing, replies, ok), ev)

def Laws.upgrade_unmoved_vends_the_ledger(w, up, ok, kept):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only, +here}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {Laws.vends(W.World{W.Args{False{}, only, here}, ledger, listing,
                replies, ups}) == I.vended(D1.ledger.deps(W.parsed(ledger))) : List<&2, String>}, up)
            case True{}:
              kp.toml.doc(P.decide(W.inputs.of(Up.next(only, W.parsed(ledger), ups), listing, replies)),
                only, ledger, ups, P.cloned(W.replies.of(Up.next(only, W.parsed(ledger), ups), replies)),
                W.judged.of(Up.next(only, W.parsed(ledger), ups), replies), ok, kept,
                M6.mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok),
                rf.good(Up.next(only, W.parsed(ledger), ups), listing, replies, ok))

# LAW: what `.gitignore` holds after the effects: the text `I.sync` gave,
# whether it was written or, being the same text, kept
law syncs_arm_add:
  for b: Bool
  for +next: String
  for +ig: String
  for +text: String
  for gs: List<&2, String>
  for +h: String
  for +a: String
  for +w: A.World
  for eb: {String.eq(next, ig) == b : Bool}
  {AP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore",
    P.put.in(AP.ignore.put(b, next, P.drops.of(gs, AP.says(h, a, w))), ".gitignore")), ig)
    == next : String}

def syncs_arm_add(b, next, ig, text, gs, h, a, w, eb):
  match b:
    case True{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(gs, AP.says(h, a, w)), ".gitignore"), P.Kept{},
        M1.tail_keep(h, a, w, gs, ".gitignore"))
        : {AP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore", _), ig) == next : String}
      Equal.sym(String, next, ig, Str.string_eq_true(next, ig, eb))
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(gs, AP.says(h, a, w)), ".gitignore"), P.Kept{},
        M1.tail_keep(h, a, w, gs, ".gitignore"))
        : {AP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore",
          P.put.one(P.Write{".gitignore", next}, ".gitignore", _)), ig) == next : String}
      {==}

# LAW: the effects of a package leave `.gitignore` holding `I.sync` over the
# edited ledger
law syncs_of:
  for +d: M.Dep
  for +h: String
  for +a: String
  for fs: List<&2, K.Source>
  for ss: List<&2, K.Item>
  for +m: M.Manifest
  for +w: A.World
  {AP.after(P.put.in(AP.effects.of(d, h, a, fs, ss, m, w), ".gitignore"), A.ignore(w))
    == M4.nxt(d, m, w) : String}

def syncs_of(d, h, a, _fs, _ss, m, w):
  syncs_arm_add(String.eq(M4.nxt(d, m, w), A.ignore(w)), M4.nxt(d, m, w), A.ignore(w),
    Rend.show(Rend.add.keep(m, d)), M4.gss(d, h, m), h, a, w, {==})

def Laws.add_syncs_allowlist(w, m, good, ok):
  %Equal.sym(P.Plan, AP.plan(w), P.Plan{AP.effects.k(AP.walked(w), w), P.Success{}},
    M1.succeeds(w, ok))
    : {AP.after(P.put.plan(_, ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(m, AP.added(w))), A.ignore(w)) : String}
  %Equal.sym(M.Dep, AP.added(w), M4.dd(w), M1.added_ok(w, ok))
    : {AP.after(P.put.in(AP.effects.k(AP.walked(w), w), ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(m, _)), A.ignore(w)) : String}
  %Equal.sym(List<&2, P.Effect>, AP.effects.k(AP.walked(w), w), M1.eff(w),
    M1.effects_is(AP.walked(w), w, M1.won(w, ok)))
    : {AP.after(P.put.in(_, ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(m, M4.dd(w))), A.ignore(w)) : String}
  %M1.good_m(w, m, good)
    : {AP.after(P.put.in(M1.eff(w), ".gitignore"), A.ignore(w))
      == I.sync(A.deps.of(Rend.add.keep(_, M4.dd(w))), A.ignore(w)) : String}
  syncs_of(M4.dd(w), M4.wh(AP.walked(w)), M6.aa(w), M1.wf(AP.walked(w)), M6.ws(AP.walked(w)),
    A.manifest.of(A.read(w)), w)

# LAW: what `.gitignore` holds after the edits: the text `I.sync` gave,
# whether it was written or, being the same text, kept
law syncs_arm_remove:
  for b: Bool
  for +next: String
  for +ignore: String
  for +text: String
  for hs: List<&2, String>
  for eb: {String.eq(next, ignore) == b : Bool}
  {RP.after(P.put.in(P.Write{"ez.toml", text} <> RP.ignore.put(b, next,
    P.drops.of(hs, [])), ".gitignore"), ignore) == next : String}

def syncs_arm_remove(b, next, ignore, text, hs, eb):
  match b:
    case True{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(hs, []), ".gitignore"), P.Kept{},
        M6.drops_keep_remove(hs, ".gitignore"))
        : {RP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore", _), ignore)
          == next : String}
      Equal.sym(String, next, ignore, Str.string_eq_true(next, ignore, eb))
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(hs, []), ".gitignore"), P.Kept{},
        M6.drops_keep_remove(hs, ".gitignore"))
        : {RP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore",
          P.put.one(P.Write{".gitignore", next}, ".gitignore", _)), ignore)
          == next : String}
      {==}

# LAW: over a ledger that names the dependency; the other arm refuses
law syncs_has:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for ok: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == False{} : Bool}
  {RP.after(P.put.plan(RP.plan.has(h, m, name, ignore), ".gitignore"), ignore)
    == I.sync(RP.deps.of(Rend.remove(m, name)), ignore) : String}

def syncs_has(h, m, name, ignore, ok):
  match h:
    case True{}:
      syncs_arm_remove(String.eq(I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore),
        I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore,
        Rend.show(Rend.remove(m, name)),
        RP.gone(RP.deps.of(m), name, RP.deps.of(Rend.remove(m, name))), {==})
    case False{}:
      Eq.bit.absurd2(&2, {RP.after(P.put.plan(RP.plan.has(False{}, m, name, ignore),
        ".gitignore"), ignore) == I.sync(RP.deps.of(Rend.remove(m, name)), ignore)
        : String}, ok)

def Laws.remove_syncs_allowlist(name, s, ignore, m, good, ok):
  %good : {RP.after(P.put.plan(RP.plan.read(_, name, ignore), ".gitignore"), ignore)
    == I.sync(RP.deps.of(Rend.remove(m, name)), ignore) : String}
  syncs_has(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))), m, name, ignore,
    Equal.trans(Bool,
      RP.refuses.plan(RP.plan.read(M.Good{m}, name, ignore)),
      RP.refuses.plan(RP.plan.read(M.parse(s), name, ignore)),
      False{},
      Equal.cong(M.Read, Bool, x => RP.refuses.plan(RP.plan.read(x, name, ignore)),
        M.Good{m}, M.parse(s), good),
      ok))
