# proofs of laws/UpgradeRewritesImports.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/upgrade.bend as U
import ../src/add/world.bend as A
import ../laws/RewriteGoesLineByLine.bend as L1
import ../laws/RewriteKeepsOtherLines.bend as L2
import ../laws/UpgradeRewritesImports.bend as Laws
import ../laws/UpgradeRewritesSources.bend as L3
import ../laws/defs/LockInputs.bend as D1
import ../laws/defs/WorldAfterLock.bend as D2
import ./lemmas/ImportLineRewrite.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2
import ./lemmas/UpgradeSourceWrites.bend as M3
import ./lemmas/UpgradeWritesAroundLedger.bend as M4

# LAW: the old hash of the first move names something
law ok_old_full:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {String.is_empty(o) == False{} : Bool}

def ok_old_full(o, n, t, ok):
  Eq.not.true(String.is_empty(o),
    Eq.and.left(Bool.not(String.is_empty(o)), D1.plain(o),
      Eq.and.left(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
        Bool.and(D1.plain(n), D2.olds.miss(t, n)),
        Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
          Bool.and(D1.plain(n), D2.olds.miss(t, n))), D2.moves.ok(t), ok))))

# LAW: and is plain
law ok_old_plain:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {D1.plain(o) == True{} : Bool}

def ok_old_plain(o, n, t, ok):
  Eq.and.right(Bool.not(String.is_empty(o)), D1.plain(o),
    Eq.and.left(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
      Bool.and(D1.plain(n), D2.olds.miss(t, n)),
      Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
        Bool.and(D1.plain(n), D2.olds.miss(t, n))), D2.moves.ok(t), ok)))

# LAW: and is no old hash of a move after it
law ok_new_miss:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {D2.olds.miss(t, n) == True{} : Bool}

def ok_new_miss(o, n, t, ok):
  Eq.and.right(D1.plain(n), D2.olds.miss(t, n),
    Eq.and.right(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
      Bool.and(D1.plain(n), D2.olds.miss(t, n)),
      Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), D1.plain(o)),
        Bool.and(D1.plain(n), D2.olds.miss(t, n))), D2.moves.ok(t), ok)))

# LAW: a plain hash holds no `/`
law plain_slash:
  for +s: String
  for e: {D1.plain(s) == True{} : Bool}
  {Str.clear(s, '/') == True{} : Bool}

def plain_slash(s, e):
  Eq.and.left(Str.clear(s, '/'), Str.clear(s, '\n'), e)

# A line names one hash at most. `import <a>/` and `import <b>/` both at the
# front of a line, with neither hash holding `/`, have `a` and `b` the same:
# the first `/` after `import ` ends both.

# LAW: a prefix check that held had heads that compared equal
law sw_if_head:
  for t: String
  for p: String
  for s: Bool
  for e: {String.starts_with.go.if(p, t, s) == True{} : Bool}
  {s == True{} : Bool}

def sw_if_head(_t, _p, s, e):
  match s:
    case True{}:
      {==}
    case False{}:
      e

# LAW: and tails that held
law sw_if_tail:
  for t: String
  for p: String
  for s: Bool
  for e: {String.starts_with.go.if(p, t, s) == True{} : Bool}
  {String.starts_with(t, p) == True{} : Bool}

def sw_if_tail(t, p, s, e):
  match s:
    case True{}:
      e
    case False{}:
      Eq.bit.absurd(&2, {String.starts_with(t, p) == True{} : Bool}, e)

# LAW: a string that starts with two joined starts, past the first, with the
# second
law sw_drop:
  for p: String
  for +x: String
  for +q: String
  for e: {String.starts_with(x, String.append(p, q)) == True{} : Bool}
  {String.starts_with(String.drop(x, String.length(p)), q) == True{} : Bool}

def sw_drop(p, x, q, e):
  match p x:
    case SNil{} SNil{}:
      e
    case SNil{} SCon{y, r}:
      e
    case SCon{c, p2} SNil{}:
      Eq.bit.absurd(&2, {String.starts_with(String.drop(SNil{}, String.length(SCon{c, p2})), q)
        == True{} : Bool}, e)
    case SCon{+c, +p2} SCon{+y, +r}:
      sw_drop(p2, r, q, sw_if_tail(r, String.append(p2, q), Char.is_eq(y, c), e))

# LAW: `/` held by a string that holds none is a contradiction
law slash_clash:
  for +c: Char
  for +y: Char
  for +b: String
  for ey: {Char.is_eq(y, '/') == True{} : Bool}
  for ec: {Char.is_eq(y, c) == True{} : Bool}
  for eb: {Str.clear(SCon{c, b}, '/') == True{} : Bool}
  Empty

def slash_clash(c, y, b, ey, ec, eb):
  Eq.bit.clash2(Equal.trans(Bool, True{}, Char.is_eq(c, '/'), False{},
    Equal.trans(Bool, True{}, Char.is_eq(y, '/'), Char.is_eq(c, '/'),
      Equal.sym(Bool, Char.is_eq(y, '/'), True{}, ey),
      Equal.cong(Char, Bool, x => Char.is_eq(x, '/'), y, c, Str.char_eq_true(y, c, ec))),
    Eq.not.true(Char.is_eq(c, '/'),
      Eq.and.left(Bool.not(Char.is_eq(c, '/')), Str.clear(b, '/'), eb))))

# LAW: two strings that hold no `/`, each followed by `/` at the front of one
# text, are one string
law sl_same:
  for +a: String
  for +b: String
  for +z: String
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for +ha: {String.starts_with(z, String.append(a, "/")) == True{} : Bool}
  for +hb: {String.starts_with(z, String.append(b, "/")) == True{} : Bool}
  {a == b : String}

def sl_same(a, b, z, ea, eb, ha, hb):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{+d, +b2}:
      match z:
        case SNil{}:
          Eq.bit.absurd(&2, {SNil{} == SCon{d, b2} : String}, ha)
        case SCon{+y, +r}:
          Empty.absurd({SNil{} == SCon{d, b2} : String},
            slash_clash(d, y, b2,
              sw_if_head(r, "", Char.is_eq(y, '/'), ha),
              sw_if_head(r, String.append(b2, "/"), Char.is_eq(y, d), hb), eb))
    case SCon{+c, +a2} SNil{}:
      match z:
        case SNil{}:
          Eq.bit.absurd(&2, {SCon{c, a2} == SNil{} : String}, ha)
        case SCon{+y, +r}:
          Empty.absurd({SCon{c, a2} == SNil{} : String},
            slash_clash(c, y, a2,
              sw_if_head(r, "", Char.is_eq(y, '/'), hb),
              sw_if_head(r, String.append(a2, "/"), Char.is_eq(y, c), ha), ea))
    case SCon{+c, +a2} SCon{+d, +b2}:
      match z:
        case SNil{}:
          Eq.bit.absurd(&2, {SCon{c, a2} == SCon{d, b2} : String}, ha)
        case SCon{+y, +r}:
          Equal.trans(String, SCon{c, a2}, SCon{d, a2}, SCon{d, b2},
            Equal.cong(Char, String, x => SCon{x, a2}, c, d,
              Equal.trans(Char, c, y, d,
                Equal.sym(Char, y, c, Str.char_eq_true(y, c,
                  sw_if_head(r, String.append(a2, "/"), Char.is_eq(y, c), ha))),
                Str.char_eq_true(y, d,
                  sw_if_head(r, String.append(b2, "/"), Char.is_eq(y, d), hb)))),
            Equal.cong(String, String, x => SCon{d, x}, a2, b2,
              sl_same(a2, b2, r,
                Eq.and.right(Bool.not(Char.is_eq(c, '/')), Str.clear(a2, '/'), ea),
                Eq.and.right(Bool.not(Char.is_eq(d, '/')), Str.clear(b2, '/'), eb),
                sw_if_tail(r, String.append(a2, "/"), Char.is_eq(y, c), ha),
                sw_if_tail(r, String.append(b2, "/"), Char.is_eq(y, d), hb))))

# LAW: a line that names two hashes that hold no `/` names one hash twice
law prefix_same:
  for +x: String
  for +a: String
  for +b: String
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for ha: {String.starts_with(x, U.reimport.head(a)) == True{} : Bool}
  for hb: {String.starts_with(x, U.reimport.head(b)) == True{} : Bool}
  {a == b : String}

def prefix_same(x, a, b, ea, eb, ha, hb):
  sl_same(a, b, String.drop(x, 7n), ea, eb,
    sw_drop("import ", x, String.append(a, "/"), ha),
    sw_drop("import ", x, String.append(b, "/"), hb))

# LAW: a line that names a plain hash names no plain hash the hash is not
law prefix_other:
  for +x: String
  for +a: String
  for +b: String
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for ha: {String.starts_with(x, U.reimport.head(a)) == True{} : Bool}
  for ne: {String.eq(b, a) == False{} : Bool}
  {String.starts_with(x, U.reimport.head(b)) == False{} : Bool}

# LAW: the same, with how the line compares to the second given as a
# parameter
law prefix_other.arm:
  for +x: String
  for +a: String
  for +b: String
  for s: Bool
  for es: {String.starts_with(x, U.reimport.head(b)) == s : Bool}
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for ha: {String.starts_with(x, U.reimport.head(a)) == True{} : Bool}
  for ne: {String.eq(b, a) == False{} : Bool}
  {String.starts_with(x, U.reimport.head(b)) == False{} : Bool}

def prefix_other.arm(x, a, b, s, es, ea, eb, ha, ne):
  match s:
    case False{}:
      es
    case True{}:
      Eq.bit.absurd2(&2, {String.starts_with(x, U.reimport.head(b)) == False{} : Bool},
        Equal.trans(Bool, True{}, String.eq(b, a), False{},
          Equal.trans(Bool, True{}, String.eq(b, b), String.eq(b, a),
            Equal.sym(Bool, String.eq(b, b), True{}, Eq.string_eq_self(b)),
            Equal.cong(String, Bool, q => String.eq(b, q), b, a,
              prefix_same(x, b, a, eb, ea, es, ha))),
          ne))

def prefix_other(x, a, b, ea, eb, ha, ne):
  prefix_other.arm(x, a, b, String.starts_with(x, U.reimport.head(b)), {==}, ea, eb, ha, ne)

# LAW: a line a move rewrote names none of the moves after it, whose old
# hashes are plain and none of which is the new hash
law names_none_new:
  for +t: List<&2, U.Swap>
  for +n: String
  for +rest: String
  for +pn: {Str.clear(n, '/') == True{} : Bool}
  for +miss: {D2.olds.miss(t, n) == True{} : Bool}
  for +ok: {D2.moves.ok(t) == True{} : Bool}
  {L2.names.none(t, String.append(U.reimport.head(n), rest)) == True{} : Bool}

def names_none_new(t, n, rest, pn, miss, ok):
  match t:
    case []:
      {==}
    case U.Swap{+o, +n2} <> +t2:
      M2.and_tt(Bool.not(String.starts_with(String.append(U.reimport.head(n), rest),
          U.reimport.head(o))),
        L2.names.none(t2, String.append(U.reimport.head(n), rest)),
        M4.not_of_false(String.starts_with(String.append(U.reimport.head(n), rest),
            U.reimport.head(o)),
          prefix_other(String.append(U.reimport.head(n), rest), n, o, pn,
            plain_slash(o, ok_old_plain(o, n2, t2, ok)),
            Eq.starts_append(U.reimport.head(n), rest),
            Eq.not.true(String.eq(o, n),
              Eq.and.left(Bool.not(String.eq(o, n)), D2.olds.miss(t2, n), miss)))),
        names_none_new(t2, n, rest, pn,
          Eq.and.right(Bool.not(String.eq(o, n)), D2.olds.miss(t2, n), miss),
          M1.ok_rest(o, n2, t2, ok)))

# the hash a move sends to, or "" for none. Law vocabulary: ez never calls it.
def some.of(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{x}:
      x

# the type that is empty where a move was found
def some.emp(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

# LAW: no move is found in no moves
law none_some:
  for +new: String
  for e: {None{} == Some{new} : Maybe<&2, String>}
  Empty

def none_some(_new, e):
  %e : some.emp(_)
  Unit{}

# LAW: a line a move names, when the move's old hash names something, is
# rewritten to start with the new hash
law line_hits:
  for +l: String
  for +o: String
  for +n: String
  for eo: {String.is_empty(o) == False{} : Bool}
  for eh: {String.starts_with(l, U.reimport.head(o)) == True{} : Bool}
  {U.reimport.line(l, o, n)
    == String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
    : String}

def line_hits(l, o, n, eo, eh):
  %Equal.sym(Bool, String.is_empty(o), False{}, eo)
    : {U.reimport.line.go(U.reimport.hit(_, l, o), l, o, n)
      == String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
      : String}
  %Equal.sym(Bool, String.starts_with(l, U.reimport.head(o)), True{}, eh)
    : {U.reimport.line.go(_, l, o, n)
      == String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
      : String}
  {==}

# LAW: one move, with whether it is the first move of the old hash given as a
# parameter: the first rewrites the line, and no move after it touches it
# again; one of another hash does not name the line, which is left for the
# moves after it
law names_new.arm:
  for c: Bool
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +l: String
  for +old: String
  for +new: String
  for ec: {String.eq(o, old) == c : Bool}
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  for to: {Bool.pick(Maybe<&2, String>, c, Some{n}, Laws.moved.to(t, old)) == Some{new}
    : Maybe<&2, String>}
  for +hit: {String.starts_with(l, U.reimport.head(old)) == True{} : Bool}
  for +pold: {Str.clear(old, '/') == True{} : Bool}
  for ih: {Laws.moved.to(t, old) == Some{new} : Maybe<&2, String>}
    -> {String.starts_with(U.reimport.many.line(t, l), U.reimport.head(new)) == True{} : Bool}
  {String.starts_with(U.reimport.many.line(t, U.reimport.line(l, o, n)),
    U.reimport.head(new)) == True{} : Bool}

def names_new.arm(c, o, n, t, l, old, new, ec, ok, to, hit, pold, ih):
  match c:
    case True{}:
      %Equal.cong(Maybe<&2, String>, String, m => some.of(m), Some{n}, Some{new}, to)
        : {String.starts_with(U.reimport.many.line(t, U.reimport.line(l, o, n)),
          U.reimport.head(_)) == True{} : Bool}
      %Equal.sym(String, U.reimport.line(l, o, n),
        String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o)))),
        line_hits(l, o, n, ok_old_full(o, n, t, ok),
          Equal.trans(Bool, String.starts_with(l, U.reimport.head(o)),
            String.starts_with(l, U.reimport.head(old)), True{},
            Equal.cong(String, Bool, q => String.starts_with(l, U.reimport.head(q)), o, old,
              Str.string_eq_true(o, old, ec)),
            hit)))
        : {String.starts_with(U.reimport.many.line(t, _), U.reimport.head(n)) == True{} : Bool}
      %Equal.sym(String,
        U.reimport.many.line(t,
          String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))),
        String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o)))),
        M1.many_keeps(t,
          String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o)))),
          names_none_new(t, n, String.drop(l, String.length(U.reimport.head(o))),
            plain_slash(n, M1.ok_new_plain(o, n, t, ok)), ok_new_miss(o, n, t, ok),
            M1.ok_rest(o, n, t, ok))))
        : {String.starts_with(_, U.reimport.head(n)) == True{} : Bool}
      Eq.starts_append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
    case False{}:
      %Equal.sym(String, U.reimport.line(l, o, n), l,
        M1.line_keeps(l, o, n,
          prefix_other(l, old, o, pold, plain_slash(o, ok_old_plain(o, n, t, ok)), hit, ec)))
        : {String.starts_with(U.reimport.many.line(t, _), U.reimport.head(new)) == True{} : Bool}
      ih(to)

# LAW: a line that names an old hash starts, after every move, with the hash
# the first move of it sends it to
law names_new:
  for ss: List<&2, U.Swap>
  for +l: String
  for +old: String
  for +new: String
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for to: {Laws.moved.to(ss, old) == Some{new} : Maybe<&2, String>}
  for +hit: {String.starts_with(l, U.reimport.head(old)) == True{} : Bool}
  for +pold: {Str.clear(old, '/') == True{} : Bool}
  {String.starts_with(U.reimport.many.line(ss, l), U.reimport.head(new)) == True{} : Bool}

def names_new(ss, l, old, new, ok, to, hit, pold):
  match ss:
    case []:
      Empty.absurd({String.starts_with(l, U.reimport.head(new)) == True{} : Bool},
        none_some(new, to))
    case U.Swap{+o, +n} <> +t:
      names_new.arm(String.eq(o, old), o, n, t, l, old, new, {==}, ok, to, hit, pold,
        x => names_new(t, l, old, new, M1.ok_rest(o, n, t, ok), x, hit, pold))

# LAW: a hash a move is found for is plain, as every old hash of the moves is
law moved_plain.arm:
  for c: Bool
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +old: String
  for +new: String
  for ec: {String.eq(o, old) == c : Bool}
  for +ok: {D2.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  for to: {Bool.pick(Maybe<&2, String>, c, Some{n}, Laws.moved.to(t, old)) == Some{new}
    : Maybe<&2, String>}
  for ih: {Laws.moved.to(t, old) == Some{new} : Maybe<&2, String>}
    -> {Str.clear(old, '/') == True{} : Bool}
  {Str.clear(old, '/') == True{} : Bool}

def moved_plain.arm(c, o, n, t, old, _new, ec, ok, to, ih):
  match c:
    case True{}:
      %Str.string_eq_true(o, old, ec) : {Str.clear(_, '/') == True{} : Bool}
      plain_slash(o, ok_old_plain(o, n, t, ok))
    case False{}:
      ih(to)

law moved_plain:
  for ss: List<&2, U.Swap>
  for +old: String
  for +new: String
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for to: {Laws.moved.to(ss, old) == Some{new} : Maybe<&2, String>}
  {Str.clear(old, '/') == True{} : Bool}

def moved_plain(ss, old, new, ok, to):
  match ss:
    case []:
      Empty.absurd({Str.clear(old, '/') == True{} : Bool}, none_some(new, to))
    case U.Swap{+o, +n} <> +t:
      moved_plain.arm(String.eq(o, old), o, n, t, old, new, {==}, ok, to,
        x => moved_plain(t, old, new, M1.ok_rest(o, n, t, ok), x))

def Laws.rewrite_names_new(ss, text, i, old, new, ok, to, hit):
  Equal.trans(Bool,
    String.starts_with(D2.line.at(String.lines(U.reimport.many(ss, text)), i),
      U.reimport.head(new)),
    String.starts_with(U.reimport.many.line(ss, D2.line.at(String.lines(text), i)),
      U.reimport.head(new)),
    True{},
    Equal.trans(Bool,
      String.starts_with(D2.line.at(String.lines(U.reimport.many(ss, text)), i),
        U.reimport.head(new)),
      String.starts_with(D2.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
        U.reimport.head(new)),
      String.starts_with(U.reimport.many.line(ss, D2.line.at(String.lines(text), i)),
        U.reimport.head(new)),
      Equal.cong(List<&2, String>, Bool,
        ls => String.starts_with(D2.line.at(ls, i), U.reimport.head(new)),
        String.lines(U.reimport.many(ss, text)),
        U.reimport.many.lines(ss, String.lines(text)),
        L1.rewrite_by_line(ss, text, ok)),
      Equal.cong(String, Bool, x => String.starts_with(x, U.reimport.head(new)),
        D2.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
        U.reimport.many.line(ss, D2.line.at(String.lines(text), i)),
        M1.at_many(ss, String.lines(text), i))),
    names_new(ss, D2.line.at(String.lines(text), i), old, new, ok, to, hit,
      moved_plain(ss, old, new, ok, to)))

def Laws.upgrade_rewrites_imports(
  w,
  at,
  text,
  pre,
  post,
  fs,
  mp,
  mq,
  bend,
  ok,
  i,
  old,
  new,
  mv,
  to,
  hit
):
  %Equal.sym(String, D2.left.at(P.put(w, at), text), U.reimport.many(D2.swaps(w), text),
    L3.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok))
    : {String.starts_with(D2.line.at(String.lines(_), i), U.reimport.head(new)) == True{} : Bool}
  Laws.rewrite_names_new(D2.swaps(w), text, i, old, new, mv, to, hit)
