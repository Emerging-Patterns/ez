# proofs of laws/ToolBinDirChosen.bend
import Base
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../laws/ToolBinDirChosen.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1

# ---------------------------------------------------------------------------
# laws/ToolBinDirChosen.bend

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

def Laws.tool_links_in_bin_dir(w, a, d, act, l, got, ok):
  Equal.trans(String, TP.link.at(TP.plan(w)), TP.link.at(TP.made(w)),
    d ++ "/" ++ TP.name(w),
    Equal.cong(TP.Plan, String, pl => TP.link.at(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
    M1.link_made(w, a, d, act, l, got))

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
