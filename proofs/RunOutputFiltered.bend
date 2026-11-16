# proofs of laws/RunOutputFiltered.bend
import Base
import ../src/ez/quiet.bend as Q
import ../laws/RunOutputFiltered.bend as Laws

def Laws.nag_dropped(h, t, e):
  %e : {Q.put(_, h, Q.go(t)) == Q.go(t) : List<&2, String>}
  {==}

def Laws.line_kept(h, t, e):
  %e : {Q.put(_, h, Q.go(t)) == h <> Q.go(t) : List<&2, String>}
  {==}

# by induction on the lines: the blank is the last step of the fold, and a
# blank offered to a fold that has kept nothing yet is dropped
def Laws.blank_tail_dropped(ls):
  match ls:
    case []:
      {==}
    case h <> t:
      %Equal.sym(Q.Tail, Q.tail.walk(List.append(&2, String, t, [""])), Q.tail.walk(t),
          Laws.blank_tail_dropped(t))
        : {Q.tail.step(h, _) == Q.tail.step(h, Q.tail.walk(t)) : Q.Tail}
      {==}

def Laws.chomp_blank_tail(_text, ls, e):
  %e : {String.join(Q.tail.out(Q.tail.walk(_)), "\n")
    == String.join(Q.tail.out(Q.tail.walk(ls)), "\n") : String}
  %Equal.sym(Q.Tail, Q.tail.walk(List.append(&2, String, ls, [""])), Q.tail.walk(ls),
      Laws.blank_tail_dropped(ls))
    : {String.join(Q.tail.out(_), "\n") == String.join(Q.tail.out(Q.tail.walk(ls)), "\n") : String}
  {==}

def Laws.filter_drops_nag(_text, h, t, e, nag):
  %e : {String.join(Q.chomp.lines(Q.go(_)), "\n")
    == String.join(Q.chomp.lines(Q.go(t)), "\n") : String}
  %Equal.sym(List<&2, String>, Q.go(h <> t), Q.go(t), Laws.nag_dropped(h, t, nag))
    : {String.join(Q.chomp.lines(_), "\n") == String.join(Q.chomp.lines(Q.go(t)), "\n") : String}
  {==}
