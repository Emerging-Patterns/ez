# `ez tool run [--entry <file>] <target>` passes every word after the target
# to the program, dropping one leading `--`. `ez run` passes every word after
# `run` to the entry ez.toml names, or `main.bend` when it names none.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ez/start.bend as S
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../src/share/args.bend as Args

# LAW: `ez run` starts bend on the entry ez.toml names, with every word after
# `run`
law run_starts_entry:
  for +t: String
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +a: String
  for +ws: List<&2, String>
  for good: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(t) : M.Read}
  for named: {False{} == String.is_empty(e) : Bool}
  {S.start(S.Run{a <> ws}, Some{t}) == S.Starts{"bend" <> (e <> ws)} : S.Start}

# LAW: and on `main.bend` when ez.toml names no entry
law run_starts_main:
  for +t: String
  for +n: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +a: String
  for +ws: List<&2, String>
  for good: {M.Good{M.Manifest{n, "", b, h, hpa, hpv, ds, ts}} == M.parse(t) : M.Read}
  {S.start(S.Run{a <> ws}, Some{t}) == S.Starts{"bend" <> ("main.bend" <> ws)}
    : S.Start}

# ---------------------------------------------------------------------------
# laws/RunPassesWords.bend: the words handed on

# LAW: `ez tool run <target> -- <words>` hands on the words after `--`
law tool_rest_dash:
  for +a: String
  for +b: String
  for +t: String
  for +ws: List<&2, String>
  for nt: {False{} == String.eq(t, "--entry") : Bool}
  {Args.tool.rest(a <> (b <> (t <> ("--" <> ws)))) == ws : List<&2, String>}

# LAW: and every word after the target when the first is not `--`
law tool_rest_word:
  for +a: String
  for +b: String
  for +t: String
  for +h: String
  for +ws: List<&2, String>
  for nt: {False{} == String.eq(t, "--entry") : Bool}
  for ne: {False{} == String.eq(h, "--") : Bool}
  {Args.tool.rest(a <> (b <> (t <> (h <> ws)))) == h <> ws : List<&2, String>}

# LAW: and none when there are none
law tool_rest_none:
  for +a: String
  for +b: String
  for +t: String
  for nt: {False{} == String.eq(t, "--entry") : Bool}
  {Args.tool.rest(a <> (b <> (t <> []))) == [] : List<&2, String>}

# LAW: and after `--entry <file>`, the words after the target that follows
law tool_rest_entry:
  for +a: String
  for +b: String
  for +f: String
  for +t: String
  for +ws: List<&2, String>
  {Args.tool.rest(a <> (b <> ("--entry" <> (f <> (t <> ws))))) == Args.undash(ws)
    : List<&2, String>}

# LAW: which the program is started with
law tool_run_passes_words:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.exit(TP.plan(w)) == TP.Exits{TP.out(w), args} : TP.Exit}

# LAW: `ez run` hands the entry every word after `run`
law run_line_rest:
  for +e: String
  for +a: String
  for +ws: List<&2, String>
  {Args.run.line(e, a <> ws) == "bend" <> (e <> ws) : List<&2, String>}
