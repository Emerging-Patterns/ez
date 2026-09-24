# tool: the proofs. `bend PROOF.bend` is the gate.
#
# The plan is `plan.v(decide(w), w)`: `decide` walks the stages a tool
# command passes (a link directory, a cache root, what the target names, its
# place, its commit, its checkout, its ledger, the binary's record) and stops,
# waits or goes on at each; on `Go` the plan is `made(w)`, and every other
# verdict is a plan with no effect that refuses. So a refusal law is a case
# split on the verdict, and a law about a plan that does not refuse is a law
# about `made(w)`, whose parts are each a function of the act, the binary's
# record and what the World resolved. A law that a condition refuses walks
# `decide` stage by stage: every stage before the one that checks it either
# stops or waits, which refuses, or goes on to the next.
import Base
import ./world.bend as TW
import ./plan.bend as TP
import ../lock/plan.bend as P
import ../lock/up.bend as Up
import ../manifest/manifest.bend as M
import ../git/git.bend as Git
import ../pkg/path.bend as Path
import ../ez/target.bend as Tgt
import ../ez/key.bend as Key
import ../ez/args.bend as Args
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# ---------------------------------------------------------------------------
# refusals

# LAW: a verdict whose plan refuses writes nothing
law quiet:
  for v: TP.Verdict
  for +w: TW.World
  for r: {TP.refuses.plan(TP.plan.v(v, w)) == True{} : Bool}
  {TP.writes(TP.plan.v(v, w)) == False{} : Bool}

def quiet(v, w, r):
  match v:
    case TP.Go{}:
      Eq.bit.absurd(&2, {TP.writes(TP.plan.v(TP.Go{}, w)) == False{} : Bool}, r)
    case TP.Wait{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}

def Laws.tool_refusal_writes_nothing(w, r):
  quiet(TP.decide(w), w, r)

# LAW: and exits 1, starting nothing
law quiet_exit:
  for v: TP.Verdict
  for +w: TW.World
  for r: {TP.refuses.plan(TP.plan.v(v, w)) == True{} : Bool}
  {TP.exit(TP.plan.v(v, w)) == TP.Refusal{} : TP.Exit}

def quiet_exit(v, w, r):
  match v:
    case TP.Go{}:
      Eq.bit.absurd(&2, {TP.exit(TP.plan.v(TP.Go{}, w)) == TP.Refusal{} : TP.Exit}, r)
    case TP.Wait{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}

def Laws.tool_refusal_exits_one(w, r):
  quiet_exit(TP.decide(w), w, r)

# LAW: a sync that refuses names nothing to install
law sync_quiet:
  for s: TP.Sync
  for r: {TP.sync.refuses(s) == True{} : Bool}
  {TP.sync.names(s) == [] : List<&2, String>}

def sync_quiet(s, r):
  match s:
    case TP.Sync{ns}:
      Eq.bit.absurd(&2, {TP.sync.names(TP.Sync{ns}) == [] : List<&2, String>}, r)
    case TP.SyncNo{_why}:
      {==}

def Laws.sync_refusal_installs_nothing(ledger, lock, r):
  sync_quiet(TP.sync(ledger, lock), r)

# ---------------------------------------------------------------------------
# a plan that does not refuse

# LAW: a verdict whose plan does not refuse is `Go`, and its plan is `made`
law plan_made:
  for v: TP.Verdict
  for +w: TW.World
  for ok: {TP.refuses.plan(TP.plan.v(v, w)) == False{} : Bool}
  {TP.plan.v(v, w) == TP.made(w) : TP.Plan}

def plan_made(v, w, ok):
  match v:
    case TP.Go{}:
      {==}
    case TP.Wait{as, us}:
      Eq.bit.absurd2(&2, {TP.plan.v(TP.Wait{as, us}, w) == TP.made(w) : TP.Plan}, ok)
    case TP.Stop{why}:
      Eq.bit.absurd2(&2, {TP.plan.v(TP.Stop{why}, w) == TP.made(w) : TP.Plan}, ok)

# LAW: so a command that does not refuse runs `made`
law made_of:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.plan(w) == TP.made(w) : TP.Plan}

def made_of(w, ok):
  plan_made(TP.decide(w), w, ok)

# ---------------------------------------------------------------------------
# EZ-TOOL-1

def Laws.bin_dir_ez(ez, xdg, home, ne):
  %ne : {Bool.pick(Maybe<&2, String>, _, TW.bin.xdg(xdg, home), Some{ez}) == Some{ez}
    : Maybe<&2, String>}
  {==}

def Laws.bin_dir_xdg(xdg, home, ne):
  %ne : {Bool.pick(Maybe<&2, String>, _, TW.bin.home(home), Some{xdg}) == Some{xdg}
    : Maybe<&2, String>}
  {==}

def Laws.bin_dir_home(home, ne):
  %ne : {Bool.pick(Maybe<&2, String>, _, None{}, Some{home ++ "/.local/bin"})
    == Some{home ++ "/.local/bin"} : Maybe<&2, String>}
  {==}

def Laws.bin_dir_none(_cache, _path):
  {==}

# LAW: the link a linking act writes, once the act is known
law link_of:
  for a: TW.Act
  for +w: TW.World
  for +d: String
  for l: {TP.links.act(a) == True{} : Bool}
  for got: {TW.bin.of(TW.env(w)) == Some{d} : Maybe<&2, String>}
  {TP.link.at(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(a, w), P.Success{}})
    == d ++ "/" ++ TP.name(w) : String}

def link_of(a, w, d, l, got):
  match a:
    case TW.Run{args}:
      Eq.bit.absurd(&2, {TP.link.at(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(TW.Run{args}, w),
        P.Success{}}) == d ++ "/" ++ TP.name(w) : String}, l)
    case TW.Install{}:
      %Equal.sym(Maybe<&2, String>, TW.bin.of(TW.env(w)), Some{d}, got)
        : {TW.text.or(_) ++ "/" ++ TP.name(w) == d ++ "/" ++ TP.name(w) : String}
      {==}
    case TW.Upgrade{}:
      %Equal.sym(Maybe<&2, String>, TW.bin.of(TW.env(w)), Some{d}, got)
        : {TW.text.or(_) ++ "/" ++ TP.name(w) == d ++ "/" ++ TP.name(w) : String}
      {==}

# LAW: the link `made` writes
law link_made:
  for +w: TW.World
  for a: TW.Act
  for +d: String
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for got: {TW.bin.of(TW.env(w)) == Some{d} : Maybe<&2, String>}
  {TP.link.at(TP.made(w)) == d ++ "/" ++ TP.name(w) : String}

def link_made(w, a, d, act, l, got):
  %Equal.sym(TW.Act, TW.act(w), a, act)
    : {TP.link.at(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(_, w), P.Success{}})
      == d ++ "/" ++ TP.name(w) : String}
  link_of(a, w, d, l, got)

def Laws.tool_links_in_bin_dir(w, a, d, act, l, got, ok):
  Equal.trans(String, TP.link.at(TP.plan(w)), TP.link.at(TP.made(w)),
    d ++ "/" ++ TP.name(w),
    Equal.cong(TP.Plan, String, pl => TP.link.at(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    link_made(w, a, d, act, l, got))

def Laws.tool_links_named(w, a, d, act, l, got, ok):
  Equal.trans(String, TP.link.at(TP.plan(w)), TP.link.at(TP.made(w)),
    d ++ "/" ++ TP.name(w),
    Equal.cong(TP.Plan, String, pl => TP.link.at(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    link_made(w, a, d, act, l, got))

def Laws.tool_needs_bin_dir(w, a, act, l, none):
  %Equal.sym(TW.Act, TW.act(w), a, act)
    : {TP.refuses.plan(TP.plan.v(TP.decide.bin(Bool.and(TP.links.act(_),
      TP.none(TW.bin.of(TW.env(w)))), w), w)) == True{} : Bool}
  %Equal.sym(Bool, TP.links.act(a), True{}, l)
    : {TP.refuses.plan(TP.plan.v(TP.decide.bin(Bool.and(_,
      TP.none(TW.bin.of(TW.env(w)))), w), w)) == True{} : Bool}
  %Equal.sym(Maybe<&2, String>, TW.bin.of(TW.env(w)), None{}, none)
    : {TP.refuses.plan(TP.plan.v(TP.decide.bin(Bool.and(True{}, TP.none(_)), w), w))
      == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# EZ-TOOL-2 and EZ-TOOL-3: built or reused

# LAW: what `made` builds turns on the record alone
law reuse_made:
  for +w: TW.World
  for hit: {TP.reuse(w) == True{} : Bool}
  {TP.builds(TP.made(w)) == False{} : Bool}

def reuse_made(w, hit):
  %Equal.sym(Bool, TP.reuse(w), True{}, hit) : {TP.makes(TP.make.of(_, w)) == False{} : Bool}
  {==}

law miss_made:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.builds(TP.made(w)) == True{} : Bool}

def miss_made(w, miss):
  %Equal.sym(Bool, TP.reuse(w), False{}, miss) : {TP.makes(TP.make.of(_, w)) == True{} : Bool}
  {==}

def Laws.tool_reuses_record(w, ok, hit):
  Equal.trans(Bool, TP.builds(TP.plan(w)), TP.builds(TP.made(w)), False{},
    Equal.cong(TP.Plan, Bool, pl => TP.builds(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    reuse_made(w, hit))

def Laws.tool_builds_on_miss(w, ok, miss):
  Equal.trans(Bool, TP.builds(TP.plan(w)), TP.builds(TP.made(w)), True{},
    Equal.cong(TP.Plan, Bool, pl => TP.builds(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    miss_made(w, miss))

# LAW: a record with no commit reuses nothing, whatever is on record
law no_rev:
  for was: Key.Key
  for +f: String
  for +b: String
  {Key.reuse(was, Key.Key{"", f, b}) == False{} : Bool}

def no_rev(was, _f, _b):
  match was:
    case Key.Key{_r0, _f0, _b0}:
      {==}

# LAW: an `and` with a False right half is False
law and_false:
  for u: Bool
  {Bool.and(u, False{}) == False{} : Bool}

def and_false(u):
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a World with no commit reuses nothing
law unrevved_miss:
  for +w: TW.World
  for none: {TP.rev(w) == "" : String}
  {TP.reuse(w) == False{} : Bool}

def unrevved_miss(w, none):
  %Equal.sym(String, TP.rev(w), "", none)
    : {Bool.and(TP.there(w), Key.reuse(TP.was(w), Key.Key{_, TP.file(w), TW.bend(w)}))
      == False{} : Bool}
  %Equal.sym(Bool, Key.reuse(TP.was(w), Key.Key{"", TP.file(w), TW.bend(w)}), False{},
    no_rev(TP.was(w), TP.file(w), TW.bend(w)))
    : {Bool.and(TP.there(w), _) == False{} : Bool}
  and_false(TP.there(w))

def Laws.tool_unrevved_builds(w, ok, none):
  Laws.tool_builds_on_miss(w, ok, unrevved_miss(w, none))

# LAW: a local path with anything in `git status` is no commit, whatever
# else holds
law dirty_go:
  for ok: Bool
  for same: Bool
  for +head: String
  {TP.local.go(ok, False{}, same, head) == "" : String}

def dirty_go(ok, _same, _head):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.local_rev_dirty(abs, top, head, ok, _status, d):
  %d : {TP.local.go(ok, _, String.eq(top, abs), head) == "" : String}
  dirty_go(ok, String.eq(top, abs), head)

def Laws.local_rev_unchecked(_abs, _top, _head, _status):
  {==}

# LAW: nor one that is not the top of its checkout
law apart_go:
  for ok: Bool
  for clean: Bool
  for +head: String
  {TP.local.go(ok, clean, False{}, head) == "" : String}

def apart_go(ok, clean, _head):
  match ok:
    case True{}:
      match clean:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def Laws.local_rev_elsewhere(_abs, _top, head, ok, status, e):
  %e : {TP.local.go(ok, String.is_empty(status), _, head) == "" : String}
  apart_go(ok, String.is_empty(status), head)

def Laws.local_rev_clean(abs, head):
  %Equal.sym(Bool, String.eq(abs, abs), True{}, Eq.string_eq_self(abs))
    : {TP.local.same(_, head) == head : String}
  {==}

# ---------------------------------------------------------------------------
# EZ-TOOL-4

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
    Equal.cong(TP.Plan, Bool, pl => TP.fetches(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
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
    Equal.cong(TP.Plan, String, pl => TP.built.lib(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    lib_made(w, miss, p))

# ---------------------------------------------------------------------------
# EZ-TOOL-5 and EZ-TOOL-6

# LAW: `made` for `run` ends with the program and the words it was given
law run_made:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  {TP.exit(TP.made(w)) == TP.Exits{TP.out(w), args} : TP.Exit}

def run_made(w, args, act):
  %Equal.sym(TW.Act, TW.act(w), TW.Run{args}, act)
    : {TP.exit.of(TP.finish.of(_, w)) == TP.Exits{TP.out(w), args} : TP.Exit}
  {==}

def Laws.tool_run_exits_with_program(w, args, act, ok):
  Equal.trans(TP.Exit, TP.exit(TP.plan(w)), TP.exit(TP.made(w)), TP.Exits{TP.out(w), args},
    Equal.cong(TP.Plan, TP.Exit, pl => TP.exit(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    run_made(w, args, act))

def Laws.tool_run_passes_words(w, args, act, ok):
  Laws.tool_run_exits_with_program(w, args, act, ok)

# LAW: a linking act never starts the program
law never_a:
  for a: TW.Act
  for +w: TW.World
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.launches(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(a, w), P.Success{}}) == False{}
    : Bool}

def never_a(a, w, l):
  match a:
    case TW.Run{args}:
      Eq.bit.absurd(&2, {TP.launches(TP.Plan{TP.lay(w), TP.make(w),
        TP.finish.of(TW.Run{args}, w), P.Success{}}) == False{} : Bool}, l)
    case TW.Install{}:
      {==}
    case TW.Upgrade{}:
      {==}

# LAW: whatever the verdict
law never:
  for v: TP.Verdict
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.launches(TP.plan.v(v, w)) == False{} : Bool}

def never(v, w, a, act, l):
  match v:
    case TP.Go{}:
      %Equal.sym(TW.Act, TW.act(w), a, act)
        : {TP.launches(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(_, w), P.Success{}})
          == False{} : Bool}
      never_a(a, w, l)
    case TP.Wait{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}

def Laws.tool_link_never_runs(w, a, act, l):
  never(TP.decide(w), w, a, act, l)

# ---------------------------------------------------------------------------
# EZ-OUT-1

def Laws.tool_refusal_status_one(w, s, r):
  Equal.cong(TP.Exit, U32, e => TP.code(e, s), TP.exit(TP.plan(w)), TP.Refusal{},
    Laws.tool_refusal_exits_one(w, r))

def Laws.tool_run_status_is_program(w, args, act, ok, s):
  Equal.cong(TP.Exit, U32, e => TP.code(e, s), TP.exit(TP.plan(w)), TP.Exits{TP.out(w), args},
    Laws.tool_run_exits_with_program(w, args, act, ok))

# LAW: a linking act ends a plan that goes on without a program
law link_ends_a:
  for a: TW.Act
  for +w: TW.World
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.exit.of(TP.finish.of(a, w)) == TP.Finished{} : TP.Exit}

def link_ends_a(a, w, l):
  match a:
    case TW.Run{args}:
      Eq.bit.absurd(&2, {TP.exit.of(TP.finish.of(TW.Run{args}, w)) == TP.Finished{}
        : TP.Exit}, l)
    case TW.Install{}:
      {==}
    case TW.Upgrade{}:
      {==}

# LAW: so `made` for `install` or `upgrade` ends without a program
law link_ends:
  for a: TW.Act
  for +w: TW.World
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.exit(TP.made(w)) == TP.Finished{} : TP.Exit}

def link_ends(a, w, act, l):
  %Equal.sym(TW.Act, TW.act(w), a, act)
    : {TP.exit.of(TP.finish.of(_, w)) == TP.Finished{} : TP.Exit}
  link_ends_a(a, w, l)

def Laws.tool_link_status_zero(w, a, act, l, ok, s):
  Equal.cong(TP.Exit, U32, e => TP.code(e, s), TP.exit(TP.plan(w)), TP.Finished{},
    Equal.trans(TP.Exit, TP.exit(TP.plan(w)), TP.exit(TP.made(w)), TP.Finished{},
      Equal.cong(TP.Plan, TP.Exit, pl => TP.exit(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
      link_ends(a, w, act, l)))

# LAW: a sync ends with the status of whether it refuses
law sync_code:
  for s: TP.Sync
  {P.status(TP.sync.outcome(s)) == P.status.of(TP.sync.refuses(s)) : U32}

def sync_code(s):
  match s:
    case TP.Sync{_ns}:
      {==}
    case TP.SyncNo{_why}:
      {==}

def Laws.sync_exits_as_it_refuses(ledger, lock):
  sync_code(TP.sync(ledger, lock))

def Laws.sync_needs_ledger(_lock):
  {==}

# ---------------------------------------------------------------------------
# EZ-TOOL-7

def Laws.file_pin_bin(pb, pe, b, e, ne):
  %ne : {TP.chosen(Bool.pick(String, _, pe, pb), b, e) == pb : String}
  %ne : {Bool.pick(String, _, Tgt.file.of(b, e), pb) == pb : String}
  {==}

def Laws.file_pin_entry(pe, b, e, ne):
  %ne : {Bool.pick(String, _, Tgt.file.of(b, e), pe) == pe : String}
  {==}

def Laws.file_bin(b, e, ne):
  %ne : {Bool.pick(String, _, Tgt.entry.or(e), b) == b : String}
  {==}

def Laws.file_entry(e, ne):
  %ne : {Bool.pick(String, _, "main.bend", e) == e : String}
  {==}

def Laws.file_main(o, b, e, zo, zb, ze):
  %Equal.sym(Bool, String.is_empty(o), True{}, zo)
    : {Bool.pick(String, _, Tgt.file.of(b, e), o) == "main.bend" : String}
  %Equal.sym(Bool, String.is_empty(b), True{}, zb)
    : {Bool.pick(String, _, Tgt.entry.or(e), b) == "main.bend" : String}
  %Equal.sym(Bool, String.is_empty(e), True{}, ze)
    : {Bool.pick(String, _, "main.bend", e) == "main.bend" : String}
  {==}

# LAW: what `made` builds on a miss is the chosen file of the checkout
law built_made:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.built(TP.made(w))
    == Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
    : String}

def built_made(w, miss):
  %Equal.sym(Bool, TP.reuse(w), False{}, miss)
    : {TP.built(TP.Plan{TP.lay(w), TP.make.of(_, w), TP.finish(w), P.Success{}})
      == Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w),
        TP.entry(w))) : String}
  {==}

def Laws.tool_builds_file(w, ok, miss):
  Equal.trans(String, TP.built(TP.plan(w)), TP.built(TP.made(w)),
    Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w))),
    Equal.cong(TP.Plan, String, pl => TP.built(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    built_made(w, miss))

def Laws.file_flag_over_ledger(f, b, e, ne):
  %ne : {Bool.pick(String, _, Tgt.file.of(b, e), f) == f : String}
  {==}

def Laws.file_pin_over_flag(o, f, b, e, ne):
  %ne : {TP.chosen(Bool.pick(String, _, f, o), b, e) == o : String}
  %ne : {Bool.pick(String, _, Tgt.file.of(b, e), o) == o : String}
  {==}

def Laws.plain_name_stem(f, u, ne):
  %ne : {Bool.pick(String, _, TP.repo.name(u), TP.stem(f)) == TP.stem(f) : String}
  {==}

def Laws.plain_name_repo(f, u, m):
  %m : {Bool.pick(String, _, TP.repo.name(u), TP.stem(f)) == TP.repo.name(u) : String}
  {==}

def Laws.tool_plain_named(w, p):
  %Equal.sym(Bool, TP.plain(w), True{}, p)
    : {TP.name.of(_, w) == TP.plain.name(TP.choice(w), TP.origin(w)) : String}
  {==}

# LAW: a checkout with no ez.toml reads as a ledger that names nothing
law none_man:
  for m: Maybe<&2, String>
  for h: {TP.none(m) == True{} : Bool}
  {TP.man.of(TP.led.of(m)) == M.Manifest{"", "", "", "", [], []} : M.Manifest}

def none_man(m, h):
  match m:
    case None{}:
      {==}
    case Some{t}:
      Eq.bit.absurd(&2, {TP.man.of(TP.led.of(Some{t})) == M.Manifest{"", "", "", "", [], []}
        : M.Manifest}, h)

# LAW: so a plain repository's ledger names no `bin` and no `entry`
law plain_man:
  for +w: TW.World
  for p: {TP.plain(w) == True{} : Bool}
  {TP.man(w) == M.Manifest{"", "", "", "", [], []} : M.Manifest}

def plain_man(w, p):
  none_man(TP.co.toml(TP.co(w)), p)

# LAW: what a plain repository that no pin names a file for builds, before
# `--entry` is read
law plain_file:
  for +w: TW.World
  for p: {TP.plain(w) == True{} : Bool}
  for free: {TP.over(w) == "" : String}
  {Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
    == Path.join(TP.top(w), TP.chosen(TW.want(w), "", "")) : String}

def plain_file(w, p, free):
  %Equal.sym(String, TP.over(w), "", free)
    : {Path.join(TP.top(w), TP.chosen(TP.wish(_, TW.want(w)), TP.bin(w), TP.entry(w)))
      == Path.join(TP.top(w), TP.chosen(TW.want(w), "", "")) : String}
  %Equal.sym(M.Manifest, TP.man(w), M.Manifest{"", "", "", "", [], []}, plain_man(w, p))
    : {Path.join(TP.top(w), TP.chosen(TW.want(w), TP.man.bin(_), TP.man.entry(_)))
      == Path.join(TP.top(w), TP.chosen(TW.want(w), "", "")) : String}
  {==}

# LAW: a plain repository with no `--entry` builds `main.bend`
law plain_main:
  for +w: TW.World
  for p: {TP.plain(w) == True{} : Bool}
  for free: {TP.over(w) == "" : String}
  for flag: {TW.want(w) == "" : String}
  {Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
    == Path.join(TP.top(w), "main.bend") : String}

def plain_main(w, p, free, flag):
  %flag
    : {Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
      == Path.join(TP.top(w), TP.chosen(_, "", "")) : String}
  plain_file(w, p, free)

def Laws.tool_plain_builds_main(w, ok, miss, p, free, flag):
  Equal.trans(String, TP.built(TP.plan(w)),
    Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w))),
    Path.join(TP.top(w), "main.bend"),
    Laws.tool_builds_file(w, ok, miss), plain_main(w, p, free, flag))

# LAW: and with `--entry`, the file it names
law plain_entry:
  for +w: TW.World
  for p: {TP.plain(w) == True{} : Bool}
  for free: {TP.over(w) == "" : String}
  for ne: {False{} == String.is_empty(TW.want(w)) : Bool}
  {Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
    == Path.join(TP.top(w), TW.want(w)) : String}

def plain_entry(w, p, free, ne):
  %Equal.sym(Bool, False{}, String.is_empty(TW.want(w)), ne)
    : {Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
      == Path.join(TP.top(w), Bool.pick(String, _, Tgt.file.of("", ""), TW.want(w))) : String}
  plain_file(w, p, free)

def Laws.tool_plain_builds_entry(w, ok, miss, p, free, ne):
  Equal.trans(String, TP.built(TP.plan(w)),
    Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w))),
    Path.join(TP.top(w), TW.want(w)),
    Laws.tool_builds_file(w, ok, miss), plain_entry(w, p, free, ne))

def Laws.out_name_own(n, ne):
  %ne : {Bool.pick(String, _, "app", n) == n : String}
  {==}

def Laws.out_name_app(n, z):
  %Equal.sym(Bool, String.is_empty(n), True{}, z) : {Bool.pick(String, _, "app", n) == "app" : String}
  {==}

# ---------------------------------------------------------------------------
# a stage that refuses makes the command refuse
#
# Each lemma below says: if the stage that checks the condition refuses,
# then so does every stage before it, since each either stops, waits, or
# goes on to the next. `pre_*` walks up to where the place is decided;
# `co_*` walks from there to where the checkout is decided.

law pre_pin:
  for ok: Bool
  for +n: String
  for +r: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.pin(ok, n, r, w), w)) == True{} : Bool}

def pre_pin(ok, _n, _r, _w, h):
  match ok:
    case True{}:
      h
    case False{}:
      {==}

law pre_src:
  for s: TP.Src
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.src(s, w), w)) == True{} : Bool}

def pre_src(s, w, h):
  match s:
    case TP.Pin{+n, _u, +r, _o}:
      pre_pin(Git.is_rev(r), n, r, w, h)
    case TP.Free{_pl}:
      h
    case TP.NoSrc{_why}:
      {==}

law pre_root:
  for m: Maybe<&2, String>
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.root(m, w), w)) == True{} : Bool}

def pre_root(m, w, h):
  match m:
    case None{}:
      {==}
    case Some{_r}:
      pre_src(TP.src(w), w, h)

law pre_bin:
  for b: Bool
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.bin(b, w), w)) == True{} : Bool}

def pre_bin(b, w, h):
  match b:
    case True{}:
      {==}
    case False{}:
      pre_root(TW.cache.of(w), w, h)

# LAW: a World whose place refuses refuses
law pre:
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses(w) == True{} : Bool}

def pre(w, h):
  pre_bin(Bool.and(TP.links.act(TW.act(w)), TP.none(TW.bin.of(TW.env(w)))), w, h)

law co_tip:
  for ok: Bool
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.tip(ok, url, w), w)) == True{} : Bool}

def co_tip(ok, _url, _w, h):
  match ok:
    case True{}:
      h
    case False{}:
      {==}

law co_said:
  for s: Up.Said
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.said(s, url, w), w)) == True{} : Bool}

def co_said(s, url, w, h):
  match s:
    case Up.Said{_text}:
      co_tip(Git.is_rev(TP.rev(w)), url, w, h)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law co_head:
  for s: TP.Src
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.head(s, url, w), w)) == True{} : Bool}

def co_head(s, url, w, h):
  match s:
    case TP.Pin{_n, _u, _r, _o}:
      h
    case TP.Free{_pl}:
      co_said(TP.head.said(w, url), url, w, h)
    case TP.NoSrc{_why}:
      {==}

law co_slug:
  for ok: Bool
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.slug(ok, url, w), w)) == True{} : Bool}

def co_slug(ok, url, w, h):
  match ok:
    case True{}:
      co_head(TP.src(w), url, w, h)
    case False{}:
      {==}

law co_loc:
  for l: TP.Loc
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.loc(l, w), w)) == True{} : Bool}

def co_loc(l, _w, h):
  match l:
    case TP.Loc{_a, _t, _h, _ok, _s}:
      h
    case TP.LocWait{_ask}:
      {==}
    case TP.LocNo{_why}:
      {==}

law co_place:
  for pl: Tgt.Place
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.place(pl, w), w)) == True{} : Bool}

def co_place(pl, w, h):
  match pl:
    case Tgt.Bad{_why}:
      {==}
    case Tgt.Local{+p}:
      co_loc(TP.loc(p, w), w, h)
    case Tgt.Remote{+url, +slug}:
      co_slug(Tgt.slug.ok(slug), url, w, h)

# ---------------------------------------------------------------------------
# EZ-TOOL-7: a package name that could not name a file

law bad_name:
  for +w: TW.World
  for bad: {TP.name.ok(TP.name.raw(w)) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.name(TP.name.ok(TP.name.raw(w)), w), w)) == True{}
    : Bool}

def bad_name(w, bad):
  %Equal.sym(Bool, TP.name.ok(TP.name.raw(w)), False{}, bad)
    : {TP.refuses.plan(TP.plan.v(TP.decide.name(_, w), w)) == True{} : Bool}
  {==}

law bad_led:
  for r: M.Read
  for +w: TW.World
  for bad: {TP.name.ok(TP.name.raw(w)) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.led(r, w), w)) == True{} : Bool}

def bad_led(r, w, bad):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      bad_name(w, bad)

law bad_co:
  for c: TP.Co
  for +w: TW.World
  for bad: {TP.name.ok(TP.name.raw(w)) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.co(c, w), w)) == True{} : Bool}

def bad_co(c, w, bad):
  match c:
    case TP.Kept{_t, _l}:
      bad_led(TP.led(w), w, bad)
    case TP.Laid{_fs}:
      bad_led(TP.led(w), w, bad)
    case TP.CoWait{_as, _us}:
      {==}
    case TP.CoNo{_why}:
      {==}

def Laws.tool_refuses_unsafe_name(w, bad):
  pre(w, co_place(TP.place(w), w, bad_co(TP.co(w), w, bad)))

# ---------------------------------------------------------------------------
# EZ-TOOL-7: a file to build that is not in the checkout
#
# `fin_*` walks from the checkout to the stage that asks whether the file is
# there: every stage before it stops, waits, or goes on to the next.

law fin_name:
  for ok: Bool
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.name(ok, w), w)) == True{} : Bool}

def fin_name(ok, _w, h):
  match ok:
    case True{}:
      h
    case False{}:
      {==}

law fin_led:
  for r: M.Read
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.led(r, w), w)) == True{} : Bool}

def fin_led(r, w, h):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      fin_name(TP.name.ok(TP.name.raw(w)), w, h)

law fin_co:
  for c: TP.Co
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.co(c, w), w)) == True{} : Bool}

def fin_co(c, w, h):
  match c:
    case TP.Kept{_t, _l}:
      fin_led(TP.led(w), w, h)
    case TP.Laid{_fs}:
      fin_led(TP.led(w), w, h)
    case TP.CoWait{_as, _us}:
      {==}
    case TP.CoNo{_why}:
      {==}

# LAW: a World whose stage that asks for the file refuses refuses
law fin:
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses(w) == True{} : Bool}

def fin(w, h):
  pre(w, co_place(TP.place(w), w, fin_co(TP.co(w), w, h)))

law gone_file:
  for open: List<&2, TW.Ask>
  for +w: TW.World
  for miss: {TP.present(w) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.file(open, w), w)) == True{} : Bool}

def gone_file(open, w, miss):
  match open:
    case []:
      %Equal.sym(Bool, TP.present(w), False{}, miss)
        : {TP.refuses.plan(TP.plan.v(TP.decide.present(_, w), w)) == True{} : Bool}
      {==}
    case _h <> _t:
      {==}

def Laws.tool_refuses_missing_entry(w, miss):
  fin(w, gone_file(TP.file.asks(w), w, miss))

def Laws.tool_missing_entry_writes_nothing(w, miss):
  Laws.tool_refusal_writes_nothing(w, Laws.tool_refuses_missing_entry(w, miss))

# ---------------------------------------------------------------------------
# EZ-TOOL-4: an ez project with no lock

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
  fin(w, lock_file(TP.file.asks(w), w, unlocked_is(w, miss, p, none)))

# ---------------------------------------------------------------------------
# EZ-TOOL-8

def Laws.remote_refuses_slug(url, slug, bad):
  %Equal.sym(Bool, Tgt.slug.ok(slug), False{}, bad)
    : {Bool.pick(Tgt.Place, _, Tgt.Remote{url, slug}, Tgt.Bad{"not a repository"})
      == Tgt.Bad{"not a repository"} : Tgt.Place}
  {==}

law slug_place:
  for +w: TW.World
  for +url: String
  for +slug: String
  for pl: {TP.place(w) == Tgt.Remote{url, slug} : Tgt.Place}
  for bad: {Tgt.slug.ok(slug) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}

def slug_place(w, url, slug, pl, bad):
  %Equal.sym(Tgt.Place, TP.place(w), Tgt.Remote{url, slug}, pl)
    : {TP.refuses.plan(TP.plan.v(TP.decide.place(_, w), w)) == True{} : Bool}
  %Equal.sym(Bool, Tgt.slug.ok(slug), False{}, bad)
    : {TP.refuses.plan(TP.plan.v(TP.decide.slug(_, url, w), w)) == True{} : Bool}
  {==}

def Laws.tool_refuses_bad_slug(w, url, slug, pl, bad):
  pre(w, slug_place(w, url, slug, pl, bad))

law nowhere_place:
  for +w: TW.World
  for +why: String
  for pl: {TP.place(w) == Tgt.Bad{why} : Tgt.Place}
  {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}

def nowhere_place(w, why, pl):
  %Equal.sym(Tgt.Place, TP.place(w), Tgt.Bad{why}, pl)
    : {TP.refuses.plan(TP.plan.v(TP.decide.place(_, w), w)) == True{} : Bool}
  {==}

def Laws.tool_refuses_nowhere(w, why, pl):
  pre(w, nowhere_place(w, why, pl))

# ---------------------------------------------------------------------------
# EZ-TOOL-9

def Laws.tool_rest_dash(_a, _b, t, ws, nt):
  %nt : {Args.undash(Args.rest(Bool.pick(List<&2, String>, _, Args.rest("--" <> ws),
    t <> ("--" <> ws)))) == ws : List<&2, String>}
  {==}

def Laws.tool_rest_word(_a, _b, t, h, ws, nt, ne):
  %nt : {Args.undash(Args.rest(Bool.pick(List<&2, String>, _, Args.rest(h <> ws),
    t <> (h <> ws)))) == h <> ws : List<&2, String>}
  %ne : {Bool.pick(List<&2, String>, _, ws, h <> ws) == h <> ws : List<&2, String>}
  {==}

def Laws.tool_rest_none(_a, _b, t, nt):
  %nt : {Args.undash(Args.rest(Bool.pick(List<&2, String>, _, Args.rest([]), t <> [])))
    == [] : List<&2, String>}
  {==}

def Laws.tool_rest_entry(_a, _b, _f, _t, _ws):
  {==}

def Laws.run_line_rest(_e, _a, _ws):
  {==}
