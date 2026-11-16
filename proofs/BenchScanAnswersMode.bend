# proofs of laws/BenchScanAnswersMode.bend
import Base
import ../src/pkg/bench/scan.bend as B
import ../laws/BenchScanAnswersMode.bend as Laws

def Laws.run_old(_mode, size, e):
  %e : {B.run.at(_, size) == "old " ++ Nat.show(B.count.old(B.lines(size))) : String}
  {==}

def Laws.run_new(_mode, size, e):
  %e : {B.run.at(_, size) == "new " ++ Nat.show(B.count.new(B.lines(size))) : String}
  {==}

def Laws.args_drop_name(_h, _t):
  {==}

def Laws.copy_keeps_length(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Laws.copy_keeps_length(t) : {1n+List.length(&2, String, B.copy(t)) == 1n+_ : Nat}
      {==}

def Laws.at_first(_h, _t):
  {==}

def Laws.at_later(_h, _t, _p):
  {==}

def Laws.at_past_end(index):
  match index:
    case 0n:
      {==}
    case 1n+_p:
      {==}
