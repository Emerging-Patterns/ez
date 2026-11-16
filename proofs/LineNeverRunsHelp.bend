# proofs of laws/LineNeverRunsHelp.bend
import Base
import shake@0.9.0.0/main.bend as Shake
import ../src/ez/line.bend as L
import ../laws/LineNeverRunsHelp.bend as Laws

# LAW: a line Shake refused shows help or is misused, whatever help it named
law err_runs_none:
  for help: Maybe<&2, List<&2, String>>
  for +app: Shake.Cli
  for err: Shake.ParseErr
  {Laws.runs.help(L.line.err(help, app, err)) == False{} : Bool}

def err_runs_none(help, _app, _err):
  match help:
    case Some{_p}:
      {==}
    case None{}:
      {==}

# LAW: a group shows help or is misused, bare or not
law group_runs_none:
  for bare: Bool
  for +app: Shake.Cli
  for +matched: Shake.Matched
  {Laws.runs.help(L.line.group(bare, app, matched)) == False{} : Bool}

def group_runs_none(bare, _app, _matched):
  match bare:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a parsed line runs its command only when that command is not help
law run_runs_none:
  for help: Bool
  for sub: L.Sub
  for +app: Shake.Cli
  for +matched: Shake.Matched
  for e: {help == L.is.help(sub) : Bool}
  {Laws.runs.help(L.line.run(help, sub, app, matched)) == False{} : Bool}

def run_runs_none(help, _sub, app, matched, e):
  match help:
    case True{}:
      group_runs_none(String.is_empty(L.path(matched)), app, matched)
    case False{}:
      %e : {_ == False{} : Bool}
      {==}

# LAW: whatever Shake made of a line, it does not run the help subcommand
law line_runs_none:
  for +app: Shake.Cli
  for parsed: Result<&2, &2, Shake.ParseErr, Shake.Matched>
  {Laws.runs.help(L.line(app, parsed)) == False{} : Bool}

def line_runs_none(app, parsed):
  match parsed:
    case Fail{+e}:
      err_runs_none(Shake.help_path(e), app, e)
    case Done{+m}:
      run_runs_none(L.is.help(L.command(L.path(m))), L.command(L.path(m)), app, m, {==})

def Laws.never_runs_help(argv):
  line_runs_none(L.spec(), Shake.parse(L.spec(), argv))

def Laws.get_bound(_found, _name, v, e):
  %e : {Maybe.default(&2, String, _, "") == v : String}
  {==}

def Laws.get_unbound(_found, _name, e):
  %e : {Maybe.default(&2, String, _, "") == "" : String}
  {==}
