# Every line `ez` is given ends one of three ways (ez/line.bend): a command
# runs, help is shown, or the line is misused. The one subcommand that names
# no command, the help a bare `ez` shows, is never the command a line runs:
# a line that names no command shows help or is refused. And a command reads
# what the line bound for a name, or nothing when it bound none. This is
# internal: it fixes ez/line.bend's reading of shake's parse, whose own
# correctness is shake's (cited in ez/line.bend's header).
import Base
import shake@0.6.0.0/main.bend as Shake
import ../src/ez/line.bend as L

# whether a line's end runs the help subcommand
def runs.help(how: L.Line) -> Bool:
  match how:
    case L.Runs{sub, _m}:
      L.is.help(sub)
    case L.Shows{_t}:
      False{}
    case L.Misuse{_t}:
      False{}

# LAW: no line ez is given runs the help subcommand
law never_runs_help:
  for argv: List<&2, String>
  {runs.help(L.line(L.spec(), Shake.parse(L.spec(), argv))) == False{} : Bool}

# LAW: a name the line bound reads as what it bound
law get_bound:
  for found: Shake.Matched
  for +name: String
  for v: String
  for e: {Some{v} == Shake.get(found, name) : Maybe<&2, String>}
  {L.get(found, name) == v : String}

# LAW: and a name it did not bind reads as nothing
law get_unbound:
  for found: Shake.Matched
  for +name: String
  for e: {None{} == Shake.get(found, name) : Maybe<&2, String>}
  {L.get(found, name) == "" : String}
