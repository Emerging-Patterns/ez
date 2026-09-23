# init: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./plan.bend as IP
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/LAWS.bend as ML
import ../manifest/PROOF.bend as MP
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# LAW: a new project's plan that refuses writes nothing
law new_quiet:
  for ok: Bool
  for +name: String
  for +at: String
  for ig: Maybe<&2, String>
  for mn: Maybe<&2, String>
  for r: {IP.refuses.plan(IP.plan.new(ok, name, at, ig, mn)) == True{} : Bool}
  {P.writes(IP.plan.new(ok, name, at, ig, mn)) == False{} : Bool}

def new_quiet(ok, name, at, ig, mn, r):
  match ok:
    case True{}:
      Eq.bit.absurd(&2, {P.writes(IP.plan.new(True{}, name, at, ig, mn)) == False{} : Bool}, r)
    case False{}:
      {==}

# A ledger that is there is the arm with no effect; one that is not refuses
# only when its ledger cannot be written, which has no effect either.
def Laws.init_refusal_writes_nothing(w, r):
  match w:
    case IP.World{n, e, led, ig, mn}:
      match led:
        case Some{s}:
          {==}
        case None{}:
          new_quiet(Rend.renderable(IP.model(IP.name.or(n), IP.entry.or(e))),
            IP.name.or(n), IP.entry.or(e), ig, mn, r)

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
def Laws.init_keeps_ledger(_name, _entry, _s, _ignore, _main):
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

# LAW: the stub, with whether the entry is ez.toml given, is never written
# over ez.toml
law stub_kept.go:
  for +at: String
  for b: Bool
  for eb: {String.eq(at, "ez.toml") == b : Bool}
  for c: Bool
  {P.put.in(IP.main.write(Bool.or(b, c), at, []), "ez.toml") == P.Kept{} : P.Wrote}

def stub_kept.go(at, b, eb, c):
  match b c:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      %Equal.sym(Bool, String.eq(at, "ez.toml"), False{}, eb)
        : {Bool.pick(P.Wrote, _, P.Put{IP.stub()}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}

# LAW: the stub, when the entry is missing, is not written over ez.toml
law main_kept:
  for mn: Maybe<&2, String>
  for +at: String
  {P.put.in(IP.main.put(mn, at, []), "ez.toml") == P.Kept{} : P.Wrote}

def main_kept(mn, at):
  match mn:
    case Some{_s}:
      {==}
    case None{}:
      stub_kept.go(at, String.eq(at, "ez.toml"), {==}, String.eq(at, ".gitignore"))

# LAW: nor is anything else a new project writes after its ledger
law rest_kept:
  for ms: List<&2, String>
  for +text: String
  for mn: Maybe<&2, String>
  for +at: String
  {P.put.in(IP.ignore.put(ms, text, IP.main.put(mn, at, [])), "ez.toml") == P.Kept{} : P.Wrote}

def rest_kept(ms, text, mn, at):
  match ms:
    case []:
      main_kept(mn, at)
    case h <> t:
      %Equal.sym(P.Wrote, P.put.in(IP.main.put(mn, at, []), "ez.toml"), P.Kept{}, main_kept(mn, at))
        : {P.put.one(P.Write{".gitignore", IP.ignored(text, h <> t)}, "ez.toml", _)
          == P.Kept{} : P.Wrote}
      {==}

# LAW: a new project's plan writes to ez.toml a ledger that reads back as the
# one it made
law new_reads:
  for ok: Bool
  for +name: String
  for +at: String
  for eok: {Rend.renderable(IP.model(name, at)) == ok : Bool}
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +text: String
  for put: {P.put.plan(IP.plan.new(ok, name, at, ig, mn), "ez.toml") == P.Put{text} : P.Wrote}
  {M.parse(text) == M.Good{IP.model(name, at)} : M.Read}

def new_reads(ok, name, at, eok, ig, mn, text, put):
  match ok:
    case False{}:
      Eq.bit.absurd(&2, {M.parse(text) == M.Good{IP.model(name, at)} : M.Read},
        kept_not_put(text, put))
    case True{}:
      +k = rest_kept(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))), IP.text.of(ig), mn, at)
      +p = Equal.trans(P.Wrote, P.Put{IP.fresh(name, at)},
        P.put.plan(IP.plan.new(True{}, name, at, ig, mn), "ez.toml"), P.Put{text},
        Equal.sym(P.Wrote, P.put.plan(IP.plan.new(True{}, name, at, ig, mn), "ez.toml"),
          P.Put{IP.fresh(name, at)},
          Equal.cong(P.Wrote, P.Wrote, w => P.put.one(P.Write{"ez.toml", IP.fresh(name, at)}, "ez.toml", w),
            P.put.in(IP.ignore.put(IP.missing(IP.rules(name), String.lines(IP.text.of(ig))),
              IP.text.of(ig), IP.main.put(mn, at, [])), "ez.toml"), P.Kept{}, k)),
        put)
      +t = Equal.cong(P.Wrote, String, w => wrote.text(w), P.Put{IP.fresh(name, at)}, P.Put{text}, p)
      %t : {M.parse(_) == M.Good{IP.model(name, at)} : M.Read}
      ML.ledger_reads_back(IP.model(name, at), eok)

# A ledger that is there leaves ez.toml as it was; one that is not is the
# ledger the plan made, which it writes only once it reads back.
def Laws.init_ledger_reads_back(n, e, led, ig, mn, text, put):
  match led:
    case Some{_s}:
      Eq.bit.absurd(&2, {M.parse(text) == M.Good{IP.model(IP.name.or(n), IP.entry.or(e))} : M.Read},
        kept_not_put(text, put))
    case None{}:
      new_reads(Rend.renderable(IP.model(IP.name.or(n), IP.entry.or(e))),
        IP.name.or(n), IP.entry.or(e), {==}, ig, mn, text, put)
