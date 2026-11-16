# proofs of laws/TestBudgetOnlyWhenSet.bend
import Base
import ../src/ez/clock.bend as Clock
import ../laws/TestBudgetOnlyWhenSet.bend as Laws

def Laws.off_when_empty(secs, e):
  %e : {Bool.not(Bool.or(_, String.eq(secs, "0"))) == False{} : Bool}
  {==}

# LAW: a bit or'd with True is True, whatever the bit
law or_true:
  for b: Bool
  {Bool.not(Bool.or(b, True{})) == False{} : Bool}

def or_true(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.off_when_zero(secs, e):
  %e : {Bool.not(Bool.or(String.is_empty(secs), _)) == False{} : Bool}
  or_true(String.is_empty(secs))

def Laws.on_otherwise(secs, e0, e1):
  %e0 : {Bool.not(Bool.or(_, String.eq(secs, "0"))) == True{} : Bool}
  %e1 : {Bool.not(Bool.or(False{}, _)) == True{} : Bool}
  {==}
