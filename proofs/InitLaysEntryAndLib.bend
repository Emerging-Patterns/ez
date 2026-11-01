# proofs of laws/InitLaysEntryAndLib.bend
import Base
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/init/plan.bend as IP
import ../laws/InitLaysEntryAndLib.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

# A fresh project fits, so its plan writes the ledger, the ignore rules when
# they are missing, and then the library and the stub; the ignore rules are
# at another path, and what is left computes.
def Laws.init_lays_src(n, d, ig, fit):
  %Equal.sym(Bool, IP.fits(IP.name.or(n), "main.bend", d), True{}, fit)
    : {P.put.plan(IP.plan.new(_, IP.name.or(n), "main.bend", d, ig, None{}, None{}), "src/lib.bend")
      == P.Put{IP.lib()} : P.Wrote}
  %Equal.sym(P.Wrote,
    P.put.in(IP.ignore.put(IP.missing(IP.rules(IP.name.or(n)), String.lines(IP.text.of(ig))), IP.text.of(ig),
      IP.files(IP.name.or(n), "main.bend", d, None{}, None{})), "src/lib.bend"),
    P.put.in(IP.files(IP.name.or(n), "main.bend", d, None{}, None{}), "src/lib.bend"),
    M1.ignore_passes(IP.missing(IP.rules(IP.name.or(n)), String.lines(IP.text.of(ig))), IP.text.of(ig),
      IP.files(IP.name.or(n), "main.bend", d, None{}, None{}), "src/lib.bend", {==}))
    : {P.put.one(P.Write{"ez.toml", IP.fresh(IP.name.or(n), "main.bend")}, "src/lib.bend", _)
      == P.Put{IP.lib()} : P.Wrote}
  {==}

def Laws.init_lays_main(n, d, ig, fit):
  %Equal.sym(Bool, IP.fits(IP.name.or(n), "main.bend", d), True{}, fit)
    : {P.put.plan(IP.plan.new(_, IP.name.or(n), "main.bend", d, ig, None{}, None{}), "main.bend")
      == P.Put{IP.stub(IP.name.or(n), d, True{})} : P.Wrote}
  %Equal.sym(P.Wrote,
    P.put.in(IP.ignore.put(IP.missing(IP.rules(IP.name.or(n)), String.lines(IP.text.of(ig))), IP.text.of(ig),
      IP.files(IP.name.or(n), "main.bend", d, None{}, None{})), "main.bend"),
    P.put.in(IP.files(IP.name.or(n), "main.bend", d, None{}, None{}), "main.bend"),
    M1.ignore_passes(IP.missing(IP.rules(IP.name.or(n)), String.lines(IP.text.of(ig))), IP.text.of(ig),
      IP.files(IP.name.or(n), "main.bend", d, None{}, None{}), "main.bend", {==}))
    : {P.put.one(P.Write{"ez.toml", IP.fresh(IP.name.or(n), "main.bend")}, "main.bend", _)
      == P.Put{IP.stub(IP.name.or(n), d, True{})} : P.Wrote}
  {==}

# LAW: the stub, when it is due, is not written over a path other than the
# entry
law main_passes:
  for +due: Bool
  for +at: String
  for +text: String
  for +path: String
  for ne: {String.eq(at, path) == False{} : Bool}
  {P.put.in(IP.main.put(due, at, text, []), path) == P.Kept{} : P.Wrote}

def main_passes(due, at, text, path, ne):
  match due:
    case True{}:
      M1.one_passes(at, text, path, P.Kept{}, ne)
    case False{}:
      {==}

# LAW: a new project with a library already there writes nothing over it
law keeps_src.go:
  for +ok: Bool
  for +name: String
  for +at: String
  for +desc: String
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +s: String
  for ne: {String.eq(at, "src/lib.bend") == False{} : Bool}
  {P.put.plan(IP.plan.new(ok, name, at, desc, ig, mn, Some{s}), "src/lib.bend") == P.Kept{} : P.Wrote}

def keeps_src.go(ok, name, at, desc, ig, mn, s, ne):
  match ok:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(P.Wrote,
        P.put.in(IP.ignore.put(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig),
          IP.files(name, at, desc, mn, Some{s})), "src/lib.bend"),
        P.put.in(IP.files(name, at, desc, mn, Some{s}), "src/lib.bend"),
        M1.ignore_passes(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig),
          IP.files(name, at, desc, mn, Some{s}), "src/lib.bend", {==}))
        : {P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, "src/lib.bend", _) == P.Kept{} : P.Wrote}
      %Equal.sym(P.Wrote, P.put.in(IP.main.put(IP.due(mn, at), at, IP.stub(name, desc, False{}), []), "src/lib.bend"),
        P.Kept{}, main_passes(IP.due(mn, at), at, IP.stub(name, desc, False{}), "src/lib.bend", ne))
        : {P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, "src/lib.bend", _) == P.Kept{} : P.Wrote}
      {==}

def Laws.init_keeps_src(n, e, d, led, ig, mn, s, ne):
  match led:
    case Some{_t}:
      {==}
    case None{}:
      keeps_src.go(IP.fits(IP.name.or(n), IP.entry.or(e), d), IP.name.or(n), IP.entry.or(e), d, ig, mn, s, ne)

# LAW: with no stub due, the library is not laid out either
law lays_off:
  for +lb: Maybe<&2, String>
  for +at: String
  {IP.lays(lb, False{}, at) == False{} : Bool}

def lays_off(lb, _at):
  match lb:
    case Some{_s}:
      {==}
    case None{}:
      {==}

# LAW: a new project with an entry already there writes nothing over it
law keeps_entry.go:
  for +ok: Bool
  for +name: String
  for +at: String
  for +desc: String
  for +ig: Maybe<&2, String>
  for +s: String
  for +lb: Maybe<&2, String>
  for nt: {String.eq("ez.toml", at) == False{} : Bool}
  for ng: {String.eq(".gitignore", at) == False{} : Bool}
  {P.put.plan(IP.plan.new(ok, name, at, desc, ig, Some{s}, lb), at) == P.Kept{} : P.Wrote}

def keeps_entry.go(ok, name, at, desc, ig, s, lb, nt, ng):
  match ok:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(P.Wrote,
        P.put.in(IP.ignore.put(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig),
          IP.files(name, at, desc, Some{s}, lb)), at),
        P.put.in(IP.files(name, at, desc, Some{s}, lb), at),
        M1.ignore_passes(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig),
          IP.files(name, at, desc, Some{s}, lb), at, ng))
        : {P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, at, _) == P.Kept{} : P.Wrote}
      %Equal.sym(Bool, IP.lays(lb, False{}, at), False{}, lays_off(lb, at))
        : {P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, at, P.put.in(IP.lib.put(_, []), at))
          == P.Kept{} : P.Wrote}
      %Equal.sym(Bool, String.eq("ez.toml", at), False{}, nt)
        : {Bool.pick(P.Wrote, _, P.Put{IP.fresh(name, at)}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}

def Laws.init_keeps_entry(n, e, d, led, ig, s, lb, nt, ng):
  match led:
    case Some{_t}:
      {==}
    case None{}:
      keeps_entry.go(IP.fits(IP.name.or(n), IP.entry.or(e), d), IP.name.or(n), IP.entry.or(e), d, ig, s, lb, nt,
        ng)
