# proofs of laws/TestOutputPicksLines.bend
import Base
import ../src/check/out.bend as O
import ../laws/TestOutputPicksLines.bend as Laws

def Laws.nonblank_drops(line, rest, empty):
  %empty : {Bool.pick(List<&2, String>, _, O.nonblank(rest), line <> O.nonblank(rest))
    == O.nonblank(rest) : List<&2, String>}
  {==}

def Laws.nonblank_keeps(line, rest, full):
  %full : {Bool.pick(List<&2, String>, _, O.nonblank(rest), line <> O.nonblank(rest))
    == line <> O.nonblank(rest) : List<&2, String>}
  {==}

def Laws.first_line(_line, _rest):
  {==}

def Laws.line_is_first(_out):
  {==}

def Laws.last_one(_line):
  {==}

def Laws.last_more(_line, _next, _rest):
  {==}

def Laws.tail_is_last(_out):
  {==}

def Laws.nth_first(_line, _rest):
  {==}

def Laws.nth_next(_line, _rest, _index):
  {==}

def Laws.starting_hit(line, rest, pre, hit):
  %hit : {O.first.step(_, line, _u => O.starting(rest, pre)) == line : String}
  {==}

def Laws.starting_miss(line, rest, pre, miss):
  %miss : {O.first.step(_, line, _u => O.starting(rest, pre)) == O.starting(rest, pre) : String}
  {==}

def Laws.containing_hit(line, rest, sub, hit):
  %hit : {O.first.step(_, line, _u => O.containing(rest, sub)) == line : String}
  {==}

def Laws.containing_miss(line, rest, sub, miss):
  %miss : {O.first.step(_, line, _u => O.containing(rest, sub)) == O.containing(rest, sub) : String}
  {==}

def Laws.value_reads(_text, _key):
  {==}

def Laws.inside_env(_at, _args):
  {==}

def Laws.ez_runs_bin(_repo, _app, _args):
  {==}
