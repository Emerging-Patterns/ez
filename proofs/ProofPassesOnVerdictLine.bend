# proofs of laws/ProofPassesOnVerdictLine.bend
import Base
import ../src/ez/verdict.bend as V
import ../laws/ProofPassesOnVerdictLine.bend as Laws

def Laws.passes_on_verdict(_text, _t, e):
  %e : {String.eq(V.head.of(_), V.verdict()) == True{} : Bool}
  {==}

def Laws.fails_otherwise(_text, _h, _t, e, ne):
  %e : {String.eq(V.head.of(_), V.verdict()) == False{} : Bool}
  %ne : {_ == False{} : Bool}
  {==}

def Laws.count_pass(_n):
  {==}

def Laws.count_fail(_n):
  {==}

def Laws.indent_lines(_text, h, t, e):
  %e : {String.concat(V.indent.go(_))
    == String.append("    " ++ h ++ "\n", String.concat(V.indent.go(t))) : String}
  {==}

def Laws.one_run_per_file(ps, cap, gigs, at):
  match ps:
    case []:
      {==}
    case +h <> t:
      %Laws.one_run_per_file(t, cap, gigs, at)
        : {1n+List.length(&2, List<&2, String>, V.cmds(t, cap, gigs, at)) == 1n+_ : Nat}
      {==}
