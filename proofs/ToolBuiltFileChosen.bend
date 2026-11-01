# proofs of laws/ToolBuiltFileChosen.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/ez/target.bend as Tgt
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../laws/ToolBuiltFileChosen.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlannerStages.bend as M2

def Laws.tool_links_named(w, a, d, act, l, got, ok):
  Equal.trans(String, TP.link.at(TP.plan(w)), TP.link.at(TP.made(w)),
    d ++ "/" ++ TP.name(w),
    Equal.cong(TP.Plan, String, pl => TP.link.at(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
    M1.link_made(w, a, d, act, l, got))

# ---------------------------------------------------------------------------
# laws/ToolBuiltFileChosen.bend

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
    Equal.cong(TP.Plan, String, pl => TP.built(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
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
  {TP.man.of(TP.led.of(m)) == M.Manifest{"", "", "", "", "", "", [], []} : M.Manifest}

def none_man(m, h):
  match m:
    case None{}:
      {==}
    case Some{t}:
      Eq.bit.absurd(&2, {TP.man.of(TP.led.of(Some{t})) == M.Manifest{"", "", "", "", "", "", [], []}
        : M.Manifest}, h)

# LAW: so a plain repository's ledger names no `bin` and no `entry`
law plain_man:
  for +w: TW.World
  for p: {TP.plain(w) == True{} : Bool}
  {TP.man(w) == M.Manifest{"", "", "", "", "", "", [], []} : M.Manifest}

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
  %Equal.sym(M.Manifest, TP.man(w), M.Manifest{"", "", "", "", "", "", [], []}, plain_man(w, p))
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
# laws/ToolBuiltFileChosen.bend: a package name that could not name a file

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
  M2.pre(w, M2.co_place(TP.place(w), w, bad_co(TP.co(w), w, bad)))
