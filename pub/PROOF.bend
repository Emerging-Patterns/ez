# pub: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./pub.bend as P
import ../git/git.bend as G
import ./LAWS.bend as Laws

# LAW: one line of the search for bend's answer. A `match` may not scrutinise
# a computed value, so the head's verdict is lifted into a parameter and
# carried alongside as an equation; the law is then applied to the verdict the
# code computes, which makes the two the same thing.
law answer_is_a_name.arm:
  for h: String
  for t: List<&2, String>
  for p: Bool
  for e: {p == P.is_name(h) : Bool}
  for ih: {P.is_name(P.answer(t)) == Laws.any_name(t) : Bool}
  {P.is_name(P.answer.step(p, h, _u => P.answer(t)))
    == Laws.any_name.step(p, _u => Laws.any_name(t)) : Bool}

def answer_is_a_name.arm(_h, _t, p, e, ih):
  match p:
    case True{}:
      %e : {_ == True{} : Bool}
      {==}
    case False{}:
      ih

def Laws.answer_is_a_name(ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      answer_is_a_name.arm(h, t, P.is_name(h), {==}, Laws.answer_is_a_name(t))

# Both decoy lines are refused on their first character: `is_name` opens with
# `String.starts_with(s, "0x")`, the literal prefix is a known constructor and
# so is the head of each literal, so the comparison computes to False before
# the length or the alphabet is reached and `Bool.and` never looks at its
# second side. Nothing is left symbolic but the tail, which is never read.
def Laws.progress_is_not_an_answer(_rest):
  {==}

def Laws.import_is_not_an_answer(_rest):
  {==}

# The verdict is a two-step cascade and each law fixes one of the steps. An
# unreadable answer fixes the outer one: rewriting the recogniser's False into
# the goal leaves `judge.said(False{}, ...)`, which is `Unread{}`, which is not
# agreement.
def Laws.unread_never_agrees(ours, theirs, e):
  %e : {P.agreed(P.judge.said(_, ours, theirs)) == False{} : Bool}
  {==}

# LAW: one arm of the cascade, with the recogniser's verdict lifted. A
# recogniser that said no ends at `Unread{}` whatever the two strings are; one
# that said yes hands the goal on to the comparison, and there the hypothesis
# rewrites the comparison's False into place and leaves `Differs{}`.
law differs_never_agrees.arm:
  for +ours: String
  for +theirs: String
  for p: Bool
  for e: {False{} == String.eq(ours, theirs) : Bool}
  {P.agreed(P.judge.said(p, ours, theirs)) == False{} : Bool}

def differs_never_agrees.arm(_ours, theirs, p, e):
  match p:
    case False{}:
      {==}
    case True{}:
      %e : {P.agreed(P.judge.go(_, theirs)) == False{} : Bool}
      {==}

def Laws.differs_never_agrees(ours, theirs, e):
  differs_never_agrees.arm(ours, theirs, P.is_name(theirs), e)

# The happy path is the other arm of the same cascade: a recogniser that
# said yes hands the goal to the comparison, and there the hypothesis
# rewrites the comparison's True into place and leaves `Agreed{}`.
def Laws.same_is_agreed(ours, theirs, e0, e1):
  %e0 : {P.agreed(P.judge.said(_, ours, theirs)) == True{} : Bool}
  %e1 : {P.agreed(P.judge.go(_, theirs)) == True{} : Bool}
  {==}

# LAW: one line of the status against both walks at once. A line that says
# nothing hands each walk on to the rest of the status, which is the induction
# hypothesis; a line that says something ends one walk at False and the other
# at True, and `Bool.not` carries the one to the other.
law clean_is_all_blank.arm:
  for t: List<&2, String>
  for q: Bool
  for ih: {P.blanks(t) == Bool.not(P.dirty.lines(t)) : Bool}
  {P.blanks.step(q, _u => P.blanks(t))
    == Bool.not(P.dirty.step(q, _u => P.dirty.lines(t))) : Bool}

def clean_is_all_blank.arm(_t, q, ih):
  match q:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.clean_is_all_blank(ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      clean_is_all_blank.arm(t, String.is_empty(h), Laws.clean_is_all_blank(t))

# An untracked line opens with a character, so `String.is_empty` computes to
# False on the constructor alone and the walk stops there. The path and the
# lines after it are never read, which is the point: no status code is
# consulted, so none can be exempt.
def Laws.untracked_is_dirty(_path, _rest):
  {==}

# A name's prefix, length or alphabet is rewritten into `Bool.and`. A
# porcelain line that names a path opens with a character, so
# `String.is_empty` computes to False and the walk stops there.

def Laws.is_name_needs_0x(s, e):
  %e : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), P.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  {==}

def Laws.is_name_needs_length(s, e0, e1):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), P.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  %e1 : {Bool.and(_, G.hex.all(String.to_list(String.drop(s, 2n))))
    == False{} : Bool}
  {==}

def Laws.is_name_needs_hex(s, e0, e1, e2):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), P.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  %e1 : {Bool.and(_, G.hex.all(String.to_list(String.drop(s, 2n))))
    == False{} : Bool}
  %e2 : {_ == False{} : Bool}
  {==}

def Laws.is_name_hex34(s, e0, e1, e2):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), P.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == True{} : Bool}
  %e1 : {Bool.and(_, G.hex.all(String.to_list(String.drop(s, 2n))))
    == True{} : Bool}
  %e2 : {_ == True{} : Bool}
  {==}

def Laws.modified_is_dirty(_path, _rest):
  {==}

def Laws.staged_is_dirty(_path, _rest):
  {==}