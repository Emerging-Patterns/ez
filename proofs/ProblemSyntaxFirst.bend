# proofs of laws/ProblemSyntaxFirst.bend
import Base
import ../laws/ProblemSyntaxFirst.bend as Laws

def Laws.problem_syntax_first(bad, miss, e):
  %e : {Bool.pick(String, _,
    Bool.pick(String, String.is_empty(miss), "", miss ++ " has no hash"), bad)
    == bad : String}
  {==}
