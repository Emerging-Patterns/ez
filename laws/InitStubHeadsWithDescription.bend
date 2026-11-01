# The entry `ez init` writes opens with the line `# <name>: <description>`,
# the description `--description` gives, or `TODO describe <name>` when none
# is given, so that line is what the hub describes the package by. A
# description holding a newline is refused, and nothing is written.
#
# This guarantee and laws/InitLaysEntryAndLib.bend are proved over the plan
# `ez init` runs. The stub is its line for the hub, a newline, and the
# program, so its first line is that line whenever the line is one line
# (`init_stub_heads`, with `line_first_cut`), and the planner refuses, with
# no effect, a project whose line is not (`init_one_line`,
# `init_refusal_writes_nothing`). The line is the description given
# (`init_header_given`) or the placeholder (`init_header_placeholder`). A
# fresh project that fits writes `src/lib.bend` and a `main.bend` that
# imports it (`init_lays_src`, `init_lays_main`); in the package that entry
# makes, `main.bend` comes before `src/lib.bend`, so the hub shows the
# entry's first line. A `src/lib.bend` or an entry that is there is left as
# it was, whatever else the World holds (`init_keeps_src`,
# `init_keeps_entry`); the law for `src/lib.bend` excepts an entry asked for
# at that path, which the entry's own text decides, and the one for the
# entry excepts ez.toml and `.gitignore`, which the plan writes itself. What
# the laws take from the interpreter is trusted in src/ez/app.bend: that it
# reads the entry and `src/lib.bend` from the paths the planner names.
import Base
import ../src/pub/blurb.bend as B
import ../src/init/plan.bend as IP

# LAW: the stub `ez init` writes opens with its line for the hub, so that line
# is what the hub describes the package by (`B.blurb` reads a file's first
# line), whether or not the stub was laid out with a library
law init_stub_heads:
  for +n: String
  for +d: String
  for +lays: Bool
  for one: {B.has.nl(IP.header(n, d)) == False{} : Bool}
  {B.line.first(IP.stub(n, d, lays)) == IP.header(n, d) : String}

# LAW: that line is `# <name>: <description>` for the description asked for
law init_header_given:
  for +n: String
  for +d: String
  for some: {String.is_empty(d) == False{} : Bool}
  {IP.header(n, d) == "# " ++ n ++ ": " ++ d : String}

# LAW: and `# <name>: TODO describe <name>` when none was
law init_header_placeholder:
  for +n: String
  {IP.header(n, "") == "# " ++ n ++ ": " ++ ("TODO describe " ++ n) : String}

# LAW: a description that would spill past the entry's first line, holding a
# newline, is refused, and so writes nothing (`init_refusal_writes_nothing`)
law init_one_line:
  for +n: String
  for +e: String
  for +d: String
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  for two: {B.has.nl(IP.header(IP.name.or(n), d)) == True{} : Bool}
  {IP.refuses(IP.World{n, e, d, None{}, ig, mn, lb}) == True{} : Bool}
