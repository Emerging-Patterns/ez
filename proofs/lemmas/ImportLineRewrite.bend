# the import rewrite, line by line: the lines a move names and the lines it
# leaves
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/ledger/upgrade.bend as U
import ../../src/add/world.bend as A
import ../../laws/RewriteByLine.bend as L1
import ../../laws/RewriteKeepsOtherLines.bend as L2
import ../../laws/defs/LockInputs.bend as D1
import ../../laws/defs/WorldAfterLock.bend as D2
import ./PlanEffectFacts.bend as M1

# Import rewriting. The text is cut at its newlines and joined back, and no
# rewritten line holds a newline, so the lines afterwards are the lines
# before, each rewritten. A line that names no moved hash is left as it is.
# A line that names one is rewritten by the first move of it, and no move
# after that one names the new hash, since a hash holds no `/`: a line that
# starts `import <a>/` and `import <b>/` has `a` and `b` the same.

# LAW: the empty line names nothing, so a move leaves it
law line_empty:
  for +o: String
  for +n: String
  {U.reimport.line("", o, n) == "" : String}

def line_empty(o, _n):
  match o:
    case SNil{}:
      {==}
    case SCon{c, r}:
      {==}

# LAW: and so does every move
law many_empty:
  for ss: List<&2, U.Swap>
  {U.reimport.many.line(ss, "") == "" : String}

def many_empty(ss):
  match ss:
    case []:
      {==}
    case U.Swap{+o, +n} <> +t:
      Equal.trans(String,
        U.reimport.many.line(t, U.reimport.line("", o, n)),
        U.reimport.many.line(t, ""),
        "",
        Equal.cong(String, String, x => U.reimport.many.line(t, x),
          U.reimport.line("", o, n), "", line_empty(o, n)),
        many_empty(t))

# LAW: the line at a place, after every line was rewritten, is the line that
# was there, rewritten
law at_many:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  for i: Nat
  {D2.line.at(U.reimport.many.lines(ss, ls), i)
    == U.reimport.many.line(ss, D2.line.at(ls, i)) : String}

def at_many(ss, ls, i):
  match ls i:
    case Nil{} _:
      Equal.sym(String, U.reimport.many.line(ss, ""), "", many_empty(ss))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      at_many(ss, t, p)

# LAW: a line a move names starts with the text the move writes in front
law head_clear:
  for +n: String
  for +en: {Str.clear(n, '\n') == True{} : Bool}
  {Str.clear(U.reimport.head(n), '\n') == True{} : Bool}

def head_clear(n, en):
  Equal.trans(Bool,
    Str.clear(String.append(n, "/"), '\n'),
    Bool.and(Str.clear(n, '\n'), Str.clear("/", '\n')),
    True{},
    Str.clear_append_eq(n, "/", '\n'),
    M1.and_tt(Str.clear(n, '\n'), Str.clear("/", '\n'), en, {==}))

# LAW: one line, with whether the move names it given as a parameter: what the
# move writes holds no newline when the line and the new hash hold none
law line_clear.arm:
  for b: Bool
  for +l: String
  for +o: String
  for +n: String
  for +el: {Str.clear(l, '\n') == True{} : Bool}
  for +en: {Str.clear(n, '\n') == True{} : Bool}
  {Str.clear(U.reimport.line.go(b, l, o, n), '\n') == True{} : Bool}

def line_clear.arm(b, l, o, n, el, en):
  match b:
    case True{}:
      Equal.trans(Bool,
        Str.clear(String.append(U.reimport.head(n),
          String.drop(l, String.length(U.reimport.head(o)))), '\n'),
        Bool.and(Str.clear(U.reimport.head(n), '\n'),
          Str.clear(String.drop(l, String.length(U.reimport.head(o))), '\n')),
        True{},
        Str.clear_append_eq(U.reimport.head(n),
          String.drop(l, String.length(U.reimport.head(o))), '\n'),
        M1.and_tt(Str.clear(U.reimport.head(n), '\n'),
          Str.clear(String.drop(l, String.length(U.reimport.head(o))), '\n'),
          head_clear(n, en),
          Str.drop_clear(l, String.length(U.reimport.head(o)), '\n', el)))
    case False{}:
      el

# LAW: the new hash is plain
law ok_new_plain:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {D1.plain(n) == True{} : Bool}

def ok_new_plain(o, n, t, ok):
  Eq.and.left(D1.plain(n), D2.olds.miss(t, n),
    Eq.and.right(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
      Bool.and(D1.plain(n), D2.olds.miss(t, n)),
      Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
        Bool.and(D1.plain(n), D2.olds.miss(t, n))), D2.moves.ok(t), ok)))

# LAW: and the moves after the first are an upgrade's moves too
law ok_rest:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {D2.moves.ok(t) == True{} : Bool}

def ok_rest(o, n, t, ok):
  Eq.and.right(Bool.and(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
    Bool.and(D1.plain(n), D2.olds.miss(t, n))), D2.moves.ok(t), ok)

# LAW: and no newline
law plain_nl:
  for +s: String
  for e: {D1.plain(s) == True{} : Bool}
  {Str.clear(s, '\n') == True{} : Bool}

def plain_nl(s, e):
  Eq.and.right(Str.clear(s, '/'), Str.clear(s, '\n'), e)

# LAW: a line put through every move holds no newline when it held none
law many_line_clear:
  for +ss: List<&2, U.Swap>
  for +l: String
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for +el: {Str.clear(l, '\n') == True{} : Bool}
  {Str.clear(U.reimport.many.line(ss, l), '\n') == True{} : Bool}

def many_line_clear(ss, l, ok, el):
  match ss:
    case []:
      el
    case U.Swap{+o, +n} <> +t:
      many_line_clear(t, U.reimport.line(l, o, n), ok_rest(o, n, t, ok),
        line_clear.arm(U.reimport.hit(String.is_empty(o), l, o), l, o, n, el,
          plain_nl(n, ok_new_plain(o, n, t, ok))))

# LAW: and so does every line
law many_lines_clear:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for +el: {Str.clear.all(ls, '\n') == True{} : Bool}
  {Str.clear.all(U.reimport.many.lines(ss, ls), '\n') == True{} : Bool}

def many_lines_clear(ss, ls, ok, el):
  match ls:
    case []:
      {==}
    case +h <> +t:
      M1.and_tt(Str.clear(U.reimport.many.line(ss, h), '\n'),
        Str.clear.all(U.reimport.many.lines(ss, t), '\n'),
        many_line_clear(ss, h, ok, Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), el)),
        many_lines_clear(ss, t, ok, Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), el)))

# LAW: the pieces of a text, rewritten and joined back, cut back into those
# rewritten pieces
law by_line.arm:
  for +ss: List<&2, U.Swap>
  for +ps: List<&2, String>
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for +ec: {Str.clear.all(ps, '\n') == True{} : Bool}
  for ne: {List.is_empty(&2, String, ps) == False{} : Bool}
  {String.split(String.join(U.reimport.many.lines(ss, ps), "\n"), '\n')
    == U.reimport.many.lines(ss, ps) : List<&2, String>}

def by_line.arm(ss, ps, ok, ec, ne):
  match ps:
    case []:
      Eq.bit.absurd2(&2, {String.split(String.join(U.reimport.many.lines(ss, []), "\n"), '\n')
        == U.reimport.many.lines(ss, []) : List<&2, String>}, ne)
    case +p <> +r:
      Str.split_join(U.reimport.many.line(ss, p), U.reimport.many.lines(ss, r), '\n',
        many_lines_clear(ss, p <> r, ok, ec))

def L1.rewrite_by_line(ss, text, ok):
  by_line.arm(ss, String.split(text, '\n'), ok, Str.split_clear(text, '\n'),
    Str.split_cons(text, '\n'))

# LAW: one move, with whether it can name anything given as a parameter,
# leaves a line that does not start with its `import <old>/`
law line_keeps.arm:
  for b: Bool
  for +l: String
  for +o: String
  for +n: String
  for e: {String.starts_with(l, U.reimport.head(o)) == False{} : Bool}
  {U.reimport.line.go(U.reimport.hit(b, l, o), l, o, n) == l : String}

def line_keeps.arm(b, l, o, n, e):
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, String.starts_with(l, U.reimport.head(o)), False{}, e)
        : {U.reimport.line.go(_, l, o, n) == l : String}
      {==}

# LAW: a line a move does not name is left as it is
law line_keeps:
  for +l: String
  for +o: String
  for +n: String
  for e: {String.starts_with(l, U.reimport.head(o)) == False{} : Bool}
  {U.reimport.line(l, o, n) == l : String}

def line_keeps(l, o, n, e):
  line_keeps.arm(String.is_empty(o), l, o, n, e)

# LAW: and a line no move names is left by all of them
law many_keeps:
  for ss: List<&2, U.Swap>
  for +l: String
  for +none: {L2.names.none(ss, l) == True{} : Bool}
  {U.reimport.many.line(ss, l) == l : String}

def many_keeps(ss, l, none):
  match ss:
    case []:
      {==}
    case U.Swap{+o, +n} <> +t:
      Equal.trans(String,
        U.reimport.many.line(t, U.reimport.line(l, o, n)),
        U.reimport.many.line(t, l),
        l,
        Equal.cong(String, String, x => U.reimport.many.line(t, x),
          U.reimport.line(l, o, n), l,
          line_keeps(l, o, n, Eq.not.true(String.starts_with(l, U.reimport.head(o)),
            Eq.and.left(Bool.not(String.starts_with(l, U.reimport.head(o))),
              L2.names.none(t, l), none)))),
        many_keeps(t, l, Eq.and.right(Bool.not(String.starts_with(l, U.reimport.head(o))),
          L2.names.none(t, l), none)))
