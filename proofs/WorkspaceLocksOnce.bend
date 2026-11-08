# proofs of laws/WorkspaceLocksOnce.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../laws/PlainLockWritesOnlyLock.bend as L1
import ../laws/WorkspaceLocksOnce.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1
import ./lemmas/PlannerStages.bend as M2

# so it is not the lock's path, which holds none
def lock_not_member(
  bb: Bool,
  +pre: String,
  eb: {String.eq(P.lockfile(), pre ++ "/ez.toml") == bb : Bool}
) -> {String.eq(P.lockfile(), pre ++ "/ez.toml") == False{} : Bool}:
  match bb:
    case False{}:
      eb
    case True{}:
      Eq.bit.absurd2(&2, {String.eq(P.lockfile(), pre ++ "/ez.toml") == False{} : Bool},
        Equal.trans(Bool, True{}, Str.clear(pre ++ "/ez.toml", '/'), False{},
          Equal.cong(String, Bool, ss => Str.clear(ss, '/'), P.lockfile(), pre ++ "/ez.toml",
            Str.string_eq_true(P.lockfile(), pre ++ "/ez.toml", eb)),
          M2.slash_member(pre)))

def Laws.plain_lock_keeps_members(w, e, pre):
  L1.plain_lock_writes_only_lock(w, e, pre ++ "/ez.toml",
    lock_not_member(String.eq(P.lockfile(), pre ++ "/ez.toml"), pre, {==}))

# ---------------------------------------------------------------------------
# one lock

def Laws.joint_lone(text, fs, files, ev):
  Equal.cong(WWorkspace.Read, J.Joint, rd => J.joint.spec(rd, text, fs, files), WWorkspace.spec.of(text),
      WWorkspace.Lone{}, ev)

def Laws.lone_locks_own(_own):
  {==}

def Laws.joint_bad_table(text, fs, files, why, ev):
  Equal.cong(WWorkspace.Read, J.Joint, rd => J.joint.spec(rd, text, fs, files), WWorkspace.spec.of(text),
      WWorkspace.Bad{why}, ev)

def Laws.joint_refused_members(text, fs, files, spec, why, ev, em):
  Equal.trans(J.Joint,
    J.joint.spec(WWorkspace.spec.of(text), text, fs, files),
    J.joint.members(WWorkspace.members(spec, WWorkspace.root.of(text), J.ledgers(fs)), text, fs, files),
    J.Clash{why},
    Equal.cong(WWorkspace.Read, J.Joint, rd => J.joint.spec(rd, text, fs, files), WWorkspace.spec.of(text),
        WWorkspace.Root{spec}, ev),
    Equal.cong(WWorkspace.Members, J.Joint, mm => J.joint.members(mm, text, fs, files),
      WWorkspace.members(spec, WWorkspace.root.of(text), J.ledgers(fs)), WWorkspace.Refused{why}, em))

def Laws.combine_when_ok(root, ms, ev):
  Equal.cong(Bool, J.Joint, bb => J.combine.go(bb, root, ms), J.ok(root, ms), True{}, ev)

def Laws.combine_refused(root, ms, ev):
  Equal.cong(Bool, J.Joint, bb => J.combine.go(bb, root, ms), J.ok(root, ms), False{}, ev)

# one dependency dropped from a list, when it is or is not of the name dropped
def without_arm(
  cc: Bool,
  +yn: String,
  +yh: String,
  +ye: String,
  +ys2: M.Source,
  +yt: List<&2, M.Dep>,
  +gone: String,
  +name: String,
  ec: {String.eq(yn, gone) == cc : Bool},
  ih: {M.find(Rend.without(yt, gone), name) == M.find(yt, name) : M.Dep},
  en: {String.eq(gone, name) == False{} : Bool}
) -> {M.find(Rend.without.put(cc, M.Dep{yn, yh, ye, ys2}, Rend.without(yt, gone)), name)
    == M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, M.find(yt, name)) : M.Dep}:
  match cc:
    case True{}:
      Equal.trans(M.Dep, M.find(Rend.without(yt, gone), name), M.find(yt, name),
        M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, M.find(yt, name)), ih,
        Equal.sym(M.Dep, M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, M.find(yt, name)),
          M.find(yt, name),
          Equal.cong(Bool, M.Dep, bb => M.find.pick(bb, M.Dep{yn, yh, ye, ys2}, M.find(yt, name)),
            String.eq(yn, name), False{},
            Equal.trans(Bool, String.eq(yn, name), String.eq(gone, name), False{},
              Equal.cong(String, Bool, ss => String.eq(ss, name), yn, gone,
                Str.string_eq_true(yn, gone, ec)), en))))
    case False{}:
      Equal.cong(M.Dep, M.Dep, dd => M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, dd),
        M.find(Rend.without(yt, gone), name), M.find(yt, name), ih)

# dropping another name leaves what a name finds as it was
def find_without(
  ys: List<&2, M.Dep>,
  +gone: String,
  +name: String,
  +en: {String.eq(gone, name) == False{} : Bool}
) -> {M.find(Rend.without(ys, gone), name) == M.find(ys, name) : M.Dep}:
  match ys:
    case []:
      {==}
    case M.Dep{+yn, +yh, +ye, +ys2} <> +yt:
      without_arm(String.eq(yn, gone), yn, yh, ye, ys2, yt, gone, name, {==},
        find_without(yt, gone, name, en), en)

# the first declaration in front, of the name or not
def firsts_arm(
  bb: Bool,
  +hd: M.Dep,
  +hn: String,
  +tl: List<&2, M.Dep>,
  +name: String,
  eb: {String.eq(hn, name) == bb : Bool},
  ih: {M.find(J.firsts(tl), name) == M.find(tl, name) : M.Dep}
) -> {M.find.pick(bb, hd, M.find(Rend.without(J.firsts(tl), hn), name))
    == M.find.pick(bb, hd, M.find(tl, name)) : M.Dep}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(M.Dep, M.find(Rend.without(J.firsts(tl), hn), name), M.find(J.firsts(tl), name),
        M.find(tl, name), find_without(J.firsts(tl), hn, name, eb), ih)

# by induction on the declarations: the one in front is found first in both,
# and past it the rest finds what it did
def Laws.firsts_find(ds, name):
  match ds:
    case []:
      {==}
    case M.Dep{+hn, +hh, +he, +hs} <> +tl:
      firsts_arm(String.eq(hn, name), M.Dep{hn, hh, he, hs}, hn, tl, name, {==},
        Laws.firsts_find(tl, name))

# one tool dropped from a list, when it is or is not of the name dropped
def tool_without_arm(
  cc: Bool,
  +yn: String,
  +ye: String,
  +yb: String,
  +ys2: M.Source,
  +yt: List<&2, M.Cli>,
  +gone: String,
  +name: String,
  ec: {String.eq(yn, gone) == cc : Bool},
  ih: {M.tool.find(J.tools.without(yt, gone), name) == M.tool.find(yt, name) : M.Cli},
  en: {String.eq(gone, name) == False{} : Bool}
) -> {M.tool.find(J.tools.without.put(cc, M.Cli{yn, ye, yb, ys2}, J.tools.without(yt, gone)), name)
    == M.tool.find.pick(String.eq(yn, name), M.Cli{yn, ye, yb, ys2}, M.tool.find(yt, name)) : M.Cli}:
  match cc:
    case True{}:
      Equal.trans(M.Cli, M.tool.find(J.tools.without(yt, gone), name), M.tool.find(yt, name),
        M.tool.find.pick(String.eq(yn, name), M.Cli{yn, ye, yb, ys2}, M.tool.find(yt, name)), ih,
        Equal.sym(M.Cli, M.tool.find.pick(String.eq(yn, name), M.Cli{yn, ye, yb, ys2}, M.tool.find(yt, name)),
          M.tool.find(yt, name),
          Equal.cong(Bool, M.Cli, bb => M.tool.find.pick(bb, M.Cli{yn, ye, yb, ys2}, M.tool.find(yt, name)),
            String.eq(yn, name), False{},
            Equal.trans(Bool, String.eq(yn, name), String.eq(gone, name), False{},
              Equal.cong(String, Bool, ss => String.eq(ss, name), yn, gone,
                Str.string_eq_true(yn, gone, ec)), en))))
    case False{}:
      Equal.cong(M.Cli, M.Cli, dd => M.tool.find.pick(String.eq(yn, name), M.Cli{yn, ye, yb, ys2}, dd),
        M.tool.find(J.tools.without(yt, gone), name), M.tool.find(yt, name), ih)

# dropping another name leaves what a name finds among the tools as it was
def tool_find_without(
  ys: List<&2, M.Cli>,
  +gone: String,
  +name: String,
  +en: {String.eq(gone, name) == False{} : Bool}
) -> {M.tool.find(J.tools.without(ys, gone), name) == M.tool.find(ys, name) : M.Cli}:
  match ys:
    case []:
      {==}
    case M.Cli{+yn, +ye, +yb, +ys2} <> +yt:
      tool_without_arm(String.eq(yn, gone), yn, ye, yb, ys2, yt, gone, name, {==},
        tool_find_without(yt, gone, name, en), en)

# the first tool in front, of the name or not
def tools_firsts_arm(
  bb: Bool,
  +hd: M.Cli,
  +hn: String,
  +tl: List<&2, M.Cli>,
  +name: String,
  eb: {String.eq(hn, name) == bb : Bool},
  ih: {M.tool.find(J.tools.firsts(tl), name) == M.tool.find(tl, name) : M.Cli}
) -> {M.tool.find.pick(bb, hd, M.tool.find(J.tools.without(J.tools.firsts(tl), hn), name))
    == M.tool.find.pick(bb, hd, M.tool.find(tl, name)) : M.Cli}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(M.Cli, M.tool.find(J.tools.without(J.tools.firsts(tl), hn), name),
        M.tool.find(J.tools.firsts(tl), name), M.tool.find(tl, name),
        tool_find_without(J.tools.firsts(tl), hn, name, eb), ih)

def Laws.tools_firsts_find(ts, name):
  match ts:
    case []:
      {==}
    case M.Cli{+hn, +he, +hb, +hs} <> +tl:
      tools_firsts_arm(String.eq(hn, name), M.Cli{hn, he, hb, hs}, hn, tl, name, {==},
        Laws.tools_firsts_find(tl, name))

def Laws.combine_needs_hub(root, ms, ev):
  Eq.and.left(J.hubs(J.root.hub(root), ms),
    Bool.and(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
      J.tools.agree(J.all.tools(root, ms))), ev)

def Laws.combine_needs_deps(root, ms, ev):
  Eq.and.left(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms)), M1.join.deps(root, ms, ev))

def Laws.combine_needs_tools(root, ms, ev):
  Eq.and.right(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
    J.tools.agree(J.all.tools(root, ms)), M1.join.rest(root, ms, ev))
