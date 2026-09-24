# init: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./plan.bend as IP
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/LAWS.bend as ML
import ../manifest/PROOF.bend as MP
import ../pub/blurb.bend as B
import ../pub/LAWS.bend as PL
import ../pub/PROOF.bend as PPr
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# LAW: a new project's plan that refuses writes nothing
law new_quiet:
  for +ok: Bool
  for +name: String
  for +at: String
  for +desc: String
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  for +r: {IP.refuses.plan(IP.plan.new(ok, name, at, desc, ig, mn, lb)) == True{} : Bool}
  {P.writes(IP.plan.new(ok, name, at, desc, ig, mn, lb)) == False{} : Bool}

def new_quiet(ok, name, at, desc, ig, mn, lb, r):
  match ok:
    case True{}:
      Eq.bit.absurd(&2, {P.writes(IP.plan.new(True{}, name, at, desc, ig, mn, lb)) == False{} : Bool}, r)
    case False{}:
      {==}

# A ledger that is there is the arm with no effect; one that is not refuses
# only when the project does not fit, which has no effect either.
def Laws.init_refusal_writes_nothing(w, r):
  match w:
    case IP.World{n, e, d, led, ig, mn, lb}:
      match led:
        case Some{s}:
          {==}
        case None{}:
          new_quiet(IP.fits(IP.name.or(n), IP.entry.or(e), d),
            IP.name.or(n), IP.entry.or(e), d, ig, mn, lb, r)

# LAW: a plan ends with the status of whether it refuses
law plan_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(IP.refuses.plan(pl)) : U32}

def plan_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.init_exits_as_it_refuses(w):
  plan_code(IP.plan(w))

# A ledger that is there picks the arm that plans nothing.
def Laws.init_keeps_ledger(_name, _entry, _desc, _s, _ignore, _main, _lib):
  {==}

# whether a path was written, and what with. Proof vocabulary.
def wrote.is(w: P.Wrote) -> Bool:
  match w:
    case P.Kept{}:
      False{}
    case P.Put{_t}:
      True{}

def wrote.text(w: P.Wrote) -> String:
  match w:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# LAW: a path left as it was is not one written
law kept_not_put:
  for +text: String
  for e: {P.Kept{} == P.Put{text} : P.Wrote}
  {wrote.is(P.Kept{}) == True{} : Bool}

def kept_not_put(text, e):
  Equal.cong(P.Wrote, Bool, w => wrote.is(w), P.Kept{}, P.Put{text}, e)

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

# LAW: the stub, with whether the entry is ez.toml given, is never written
# over ez.toml
law stub_kept.go:
  for +at: String
  for +text: String
  for +b: Bool
  for eb: {String.eq(at, "ez.toml") == b : Bool}
  for +c: Bool
  {P.put.in(IP.main.put(Bool.not(Bool.or(b, c)), at, text, []), "ez.toml") == P.Kept{} : P.Wrote}

def stub_kept.go(at, text, b, eb, c):
  match b c:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      %Equal.sym(Bool, String.eq(at, "ez.toml"), False{}, eb)
        : {Bool.pick(P.Wrote, _, P.Put{text}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}

# LAW: the stub, when it is due, is not written over ez.toml
law main_kept:
  for +mn: Maybe<&2, String>
  for +at: String
  for +text: String
  {P.put.in(IP.main.put(IP.due(mn, at), at, text, []), "ez.toml") == P.Kept{} : P.Wrote}

def main_kept(mn, at, text):
  match mn:
    case Some{_s}:
      {==}
    case None{}:
      stub_kept.go(at, text, String.eq(at, "ez.toml"), {==}, String.eq(at, ".gitignore"))

# LAW: the library, laid out or not, is not written over ez.toml, and leaves
# it to the stub
law lib_kept:
  for +l: Bool
  for +mn: Maybe<&2, String>
  for +at: String
  for +text: String
  {P.put.in(IP.lib.put(l, IP.main.put(IP.due(mn, at), at, text, [])), "ez.toml") == P.Kept{} : P.Wrote}

def lib_kept(l, mn, at, text):
  match l:
    case True{}:
      %Equal.sym(P.Wrote, P.put.in(IP.main.put(IP.due(mn, at), at, text, []), "ez.toml"), P.Kept{},
        main_kept(mn, at, text))
        : {P.put.one(P.Write{"src/lib.bend", IP.lib()}, "ez.toml", _) == P.Kept{} : P.Wrote}
      {==}
    case False{}:
      main_kept(mn, at, text)

# LAW: nor is anything else a new project writes after its ledger
law rest_kept:
  for +ms: List<&2, String>
  for +text: String
  for +name: String
  for +at: String
  for +desc: String
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  {P.put.in(IP.ignore.put(ms, text, IP.files(name, at, desc, mn, lb)), "ez.toml") == P.Kept{} : P.Wrote}

def rest_kept(ms, text, name, at, desc, mn, lb):
  %Equal.sym(P.Wrote, P.put.in(IP.ignore.put(ms, text, IP.files(name, at, desc, mn, lb)), "ez.toml"),
    P.put.in(IP.files(name, at, desc, mn, lb), "ez.toml"),
    ignore_passes(ms, text, IP.files(name, at, desc, mn, lb), "ez.toml", {==}))
    : {_ == P.Kept{} : P.Wrote}
  lib_kept(IP.lays(lb, IP.due(mn, at), at), mn, at, IP.stub(name, desc, IP.lays(lb, IP.due(mn, at), at)))

# LAW: a new project's plan writes to ez.toml a ledger that reads back as the
# one it made
law new_reads:
  for +ok: Bool
  for +name: String
  for +at: String
  for +desc: String
  for eok: {IP.fits(name, at, desc) == ok : Bool}
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  for +text: String
  for put: {P.put.plan(IP.plan.new(ok, name, at, desc, ig, mn, lb), "ez.toml") == P.Put{text} : P.Wrote}
  {M.parse(text) == M.Good{IP.model(name, at)} : M.Read}

def new_reads(ok, name, at, desc, eok, ig, mn, lb, text, put):
  match ok:
    case False{}:
      Eq.bit.absurd(&2, {M.parse(text) == M.Good{IP.model(name, at)} : M.Read},
        kept_not_put(text, put))
    case True{}:
      +k = rest_kept(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig), name, at, desc,
        mn, lb)
      +p = Equal.trans(P.Wrote, P.Put{IP.fresh(name, at)},
        P.put.plan(IP.plan.new(True{}, name, at, desc, ig, mn, lb), "ez.toml"), P.Put{text},
        Equal.sym(P.Wrote, P.put.plan(IP.plan.new(True{}, name, at, desc, ig, mn, lb), "ez.toml"),
          P.Put{IP.fresh(name, at)},
          Equal.cong(P.Wrote, P.Wrote, w => P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, "ez.toml", w),
            P.put.in(IP.ignore.put(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))),
              IP.text.of(ig), IP.files(name, at, desc, mn, lb)), "ez.toml"), P.Kept{}, k)),
        put)
      +t = Equal.cong(P.Wrote, String, w => wrote.text(w), P.Put{IP.fresh(name, at)}, P.Put{text}, p)
      %t : {M.parse(_) == M.Good{IP.model(name, at)} : M.Read}
      ML.ledger_reads_back(IP.model(name, at),
        Eq.and.left(Rend.renderable(IP.model(name, at)), Bool.not(B.has.nl(IP.header(name, desc))), eok))

# A ledger that is there leaves ez.toml as it was; one that is not is the
# ledger the plan made, which it writes only once the project fits.
def Laws.init_ledger_reads_back(n, e, d, led, ig, mn, lb, text, put):
  match led:
    case Some{_s}:
      Eq.bit.absurd(&2, {M.parse(text) == M.Good{IP.model(IP.name.or(n), IP.entry.or(e))} : M.Read},
        kept_not_put(text, put))
    case None{}:
      new_reads(IP.fits(IP.name.or(n), IP.entry.or(e), d),
        IP.name.or(n), IP.entry.or(e), d, {==}, ig, mn, lb, text, put)

def Laws.init_publishes_by_hash(_n, _e):
  {==}

# ---------------------------------------------------------------------------
# the layout

# The stub is its line for the hub, a newline, then the program.
def Laws.init_stub_heads(n, d, lays, one):
  PL.line_first_cut(IP.header(n, d), IP.body(lays), one)

def Laws.init_header_given(n, d, some):
  %Equal.sym(Bool, String.is_empty(d), False{}, some)
    : {"# " ++ n ++ ": " ++ Bool.pick(String, _, "TODO describe " ++ n, d) == "# " ++ n ++ ": " ++ d : String}
  {==}

def Laws.init_header_placeholder(_n):
  {==}

# LAW: a project whose line for the hub is not one line refuses, whether or
# not its ledger reads back
law unfit_refuses:
  for +r: Bool
  for +name: String
  for +at: String
  for +desc: String
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  {IP.refuses.plan(IP.plan.new(Bool.and(r, False{}), name, at, desc, ig, mn, lb)) == True{} : Bool}

def unfit_refuses(r, _name, _at, _desc, _ig, _mn, _lb):
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.init_one_line(n, e, d, ig, mn, lb, two):
  %Equal.sym(Bool, B.has.nl(IP.header(IP.name.or(n), d)), True{}, two)
    : {IP.refuses.plan(IP.plan.new(Bool.and(Rend.renderable(IP.model(IP.name.or(n), IP.entry.or(e))), Bool.not(_)),
      IP.name.or(n), IP.entry.or(e), d, ig, mn, lb)) == True{} : Bool}
  unfit_refuses(Rend.renderable(IP.model(IP.name.or(n), IP.entry.or(e))), IP.name.or(n), IP.entry.or(e), d, ig,
    mn, lb)

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
    ignore_passes(IP.missing(IP.rules(IP.name.or(n)), String.lines(IP.text.of(ig))), IP.text.of(ig),
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
    ignore_passes(IP.missing(IP.rules(IP.name.or(n)), String.lines(IP.text.of(ig))), IP.text.of(ig),
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
      one_passes(at, text, path, P.Kept{}, ne)
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
        ignore_passes(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig),
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
        ignore_passes(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig),
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
