# proofs of laws/RunPassesWords.bend
import Base
import ../src/ez/start.bend as S
import ../src/share/args.bend as Args
import ../laws/RunPassesWords.bend as Laws
import ../laws/ToolRunExitsWithProgram.bend as L1
import ./lemmas/LockPlannerFacts.bend as M1

def Laws.run_starts_entry(_t, _n, e, _b, _h, _hpa, _hpv, _ds, _ts, a, ws, good, named):
  %good : {S.read(S.Run{a <> ws}, _) == S.Starts{"bend" <> (e <> ws)} : S.Start}
  %named : {S.Starts{"bend" <> (Bool.pick(String, _, "main.bend", e) <> ws)}
    == S.Starts{"bend" <> (e <> ws)} : S.Start}
  {==}

def Laws.run_starts_main(_t, _n, _b, _h, _hpa, _hpv, _ds, _ts, a, ws, good):
  %good : {S.read(S.Run{a <> ws}, _) == S.Starts{"bend" <> ("main.bend" <> ws)}
    : S.Start}
  {==}

def Laws.tool_run_passes_words(w, args, act, ok):
  L1.tool_run_exits_with_program(w, args, act, ok)

# ---------------------------------------------------------------------------
# laws/RunPassesWords.bend

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
