# proofs of laws/ToolTargetBuildsPin.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/git/git.bend as Git
import ../src/lock/up.bend as Up
import ../src/ez/target.bend as Tgt
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../laws/ToolTargetBuildsPin.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlannerStages.bend as M2

def Laws.local_rev_clean(abs, head):
  %Equal.sym(Bool, String.eq(abs, abs), True{}, Eq.string_eq_self(abs))
    : {TP.local.same(_, head) == head : String}
  {==}

# ---------------------------------------------------------------------------
# laws/ToolTargetBuildsPin.bend

def Laws.tool_pin_src(w, m, body, led, named, lock, pinned):
  %Equal.sym(M.Read, TW.project(w), M.Good{m}, led)
    : {TP.src.read(_, w) == TP.Pin{TW.target(w),
      M.source.url(M.tool.source(TP.pin.in(body, TW.target(w)))),
      M.source.rev(M.tool.source(TP.pin.in(body, TW.target(w)))),
      TP.over.of(M.tool.bin(TP.pin.in(body, TW.target(w))),
        M.tool.entry(TP.pin.in(body, TW.target(w))))} : TP.Src}
  %Equal.sym(Bool, TP.unpinned(m, TW.target(w)), False{}, named)
    : {TP.src.pick(_, w) == TP.Pin{TW.target(w),
      M.source.url(M.tool.source(TP.pin.in(body, TW.target(w)))),
      M.source.rev(M.tool.source(TP.pin.in(body, TW.target(w)))),
      TP.over.of(M.tool.bin(TP.pin.in(body, TW.target(w))),
        M.tool.entry(TP.pin.in(body, TW.target(w))))} : TP.Src}
  %Equal.sym(Maybe<&2, String>, TW.lock(w), Some{body}, lock)
    : {TP.pinned(_, TW.target(w)) == TP.Pin{TW.target(w),
      M.source.url(M.tool.source(TP.pin.in(body, TW.target(w)))),
      M.source.rev(M.tool.source(TP.pin.in(body, TW.target(w)))),
      TP.over.of(M.tool.bin(TP.pin.in(body, TW.target(w))),
        M.tool.entry(TP.pin.in(body, TW.target(w))))} : TP.Src}
  %Equal.sym(Bool, String.is_empty(M.tool.name(TP.pin.in(body, TW.target(w)))), False{}, pinned)
    : {TP.pin.go(_, TP.pin.in(body, TW.target(w)), TW.target(w)) == TP.Pin{TW.target(w),
      M.source.url(M.tool.source(TP.pin.in(body, TW.target(w)))),
      M.source.rev(M.tool.source(TP.pin.in(body, TW.target(w)))),
      TP.over.of(M.tool.bin(TP.pin.in(body, TW.target(w))),
        M.tool.entry(TP.pin.in(body, TW.target(w))))} : TP.Src}
  {==}

def Laws.tool_pin_rev(w, n, u, r, o, s):
  %Equal.sym(TP.Src, TP.src(w), TP.Pin{n, u, r, o}, s) : {TP.rev.of(_, w) == r : String}
  {==}

def Laws.tool_pin_url(w, n, u, r, o, s):
  %Equal.sym(TP.Src, TP.src(w), TP.Pin{n, u, r, o}, s)
    : {TP.place.of(_) == TP.place.pin(Tgt.classify(u)) : Tgt.Place}
  {==}

def Laws.tool_pin_over(w, n, u, r, o, s):
  %Equal.sym(TP.Src, TP.src(w), TP.Pin{n, u, r, o}, s) : {TP.over.src(_) == o : String}
  {==}

def Laws.tool_free_src(w, m, led, free):
  %Equal.sym(M.Read, TW.project(w), M.Good{m}, led)
    : {TP.src.read(_, w) == TP.Free{Tgt.classify(TW.target(w))} : TP.Src}
  %Equal.sym(Bool, TP.unpinned(m, TW.target(w)), True{}, free)
    : {TP.src.pick(_, w) == TP.Free{Tgt.classify(TW.target(w))} : TP.Src}
  {==}

def Laws.tool_free_rev(w, url, slug, text, s, said):
  %Equal.sym(TP.Src, TP.src(w), TP.Free{Tgt.Remote{url, slug}}, s)
    : {TP.rev.of(_, w) == Git.tip.rev(Git.rows(String.lines(text))) : String}
  %Equal.sym(Up.Said, TP.head.said(w, url), Up.Said{text}, said)
    : {TP.head.rev(_) == Git.tip.rev(Git.rows(String.lines(text))) : String}
  {==}

def Laws.tool_path_rev(w, p, abs, top, head, ok, status, s, l):
  %Equal.sym(TP.Src, TP.src(w), TP.Free{Tgt.Local{p}}, s)
    : {TP.rev.of(_, w) == TP.local.rev(abs, top, head, ok, status) : String}
  %Equal.sym(TP.Loc, TP.loc(p, w), TP.Loc{abs, top, head, ok, status}, l)
    : {TP.loc.rev(_) == TP.local.rev(abs, top, head, ok, status) : String}
  {==}

# LAW: `made` for a plain repository fetches no lock
law nolock_made:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == True{} : Bool}
  {TP.fetches(TP.made(w)) == False{} : Bool}

def nolock_made(w, miss, p):
  %Equal.sym(Bool, TP.reuse(w), False{}, miss)
    : {TP.fetches(TP.Plan{TP.lay(w), TP.make.of(_, w), TP.finish(w), P.Success{}}) == False{}
      : Bool}
  %Equal.sym(Bool, TP.plain(w), True{}, p) : {Bool.not(_) == False{} : Bool}
  {==}

def Laws.tool_plain_no_lock(w, ok, miss, p):
  Equal.trans(Bool, TP.fetches(TP.plan(w)), TP.fetches(TP.made(w)), False{},
    Equal.cong(TP.Plan, Bool, pl => TP.fetches(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
    nolock_made(w, miss, p))

# LAW: and builds with the library beside its binaries
law lib_made:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == True{} : Bool}
  {TP.built.lib(TP.made(w)) == TP.dir(w) ++ "/lib" : String}

def lib_made(w, miss, p):
  %Equal.sym(Bool, TP.reuse(w), False{}, miss)
    : {TP.built.lib(TP.Plan{TP.lay(w), TP.make.of(_, w), TP.finish(w), P.Success{}})
      == TP.dir(w) ++ "/lib" : String}
  %Equal.sym(Bool, TP.plain(w), True{}, p)
    : {Bool.pick(String, _, TP.dir(w) ++ "/lib", TP.lib.of(TP.place(w), w))
      == TP.dir(w) ++ "/lib" : String}
  {==}

def Laws.tool_plain_lib(w, ok, miss, p):
  Equal.trans(String, TP.built.lib(TP.plan(w)), TP.built.lib(TP.made(w)), TP.dir(w) ++ "/lib",
    Equal.cong(TP.Plan, String, pl => TP.built.lib(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
    lib_made(w, miss, p))

# ---------------------------------------------------------------------------
# laws/ToolTargetBuildsPin.bend: an ez project with no lock

# LAW: an ez project with no lock, whose binary is to be built, is unlocked
law unlocked_is:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == False{} : Bool}
  for none: {TP.co.lock(TP.co(w)) == None{} : Maybe<&2, String>}
  {TP.unlocked(w) == True{} : Bool}

def unlocked_is(w, miss, p, none):
  %Equal.sym(Bool, TP.reuse(w), False{}, miss)
    : {Bool.and(Bool.not(_), Bool.and(Bool.not(TP.plain(w)), TP.none(TP.co.lock(TP.co(w)))))
      == True{} : Bool}
  %Equal.sym(Bool, TP.plain(w), False{}, p)
    : {Bool.and(True{}, Bool.and(Bool.not(_), TP.none(TP.co.lock(TP.co(w))))) == True{} : Bool}
  %Equal.sym(Maybe<&2, String>, TP.co.lock(TP.co(w)), None{}, none)
    : {Bool.and(True{}, Bool.and(True{}, TP.none(_))) == True{} : Bool}
  {==}

law lock_cache:
  for open: List<&2, TW.Ask>
  for +w: TW.World
  for u: {TP.unlocked(w) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.cache(open, w), w)) == True{} : Bool}

def lock_cache(open, w, u):
  match open:
    case []:
      %Equal.sym(Bool, TP.unlocked(w), True{}, u)
        : {TP.refuses.plan(TP.plan.v(TP.decide.lock(_, w), w)) == True{} : Bool}
      {==}
    case _h <> _t:
      {==}

law lock_present:
  for ok: Bool
  for +w: TW.World
  for u: {TP.unlocked(w) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.present(ok, w), w)) == True{} : Bool}

def lock_present(ok, w, u):
  match ok:
    case True{}:
      lock_cache(TP.cache.asks(w), w, u)
    case False{}:
      {==}

law lock_file:
  for open: List<&2, TW.Ask>
  for +w: TW.World
  for u: {TP.unlocked(w) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.file(open, w), w)) == True{} : Bool}

def lock_file(open, w, u):
  match open:
    case []:
      lock_present(TP.present(w), w, u)
    case _h <> _t:
      {==}

def Laws.tool_ledger_needs_lock(w, miss, p, none):
  M2.fin(w, lock_file(TP.file.asks(w), w, unlocked_is(w, miss, p, none)))
