# proofs of laws/InitStubHeadsWithDescription.bend
import Base
import ../src/ledger/render.bend as Rend
import ../src/pub/blurb.bend as B
import ../src/init/plan.bend as IP
import ../laws/InitStubHeadsWithDescription.bend as Laws
import ../laws/PublishSaysDescription.bend as L1
import ./lemmas/PlanEffectFacts.bend as M1

# ---------------------------------------------------------------------------
# the layout

# The stub is its line for the hub, a newline, then the program.
def Laws.init_stub_heads(n, d, lays, one):
  L1.line_first_cut(IP.header(n, d), IP.body(lays), one)

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
