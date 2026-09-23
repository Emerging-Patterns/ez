# lock/world: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./world.bend as W
import ../lock.bend as L
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../../check/eq.bend as Eq
import ./LAWS.bend as Laws

# The plan is the plan of the Inputs, so equal Inputs are equal plans.
def Laws.plan_frame(w1, w2, e):
  Equal.cong(W.Inputs, W.Outcome, ins => W.plan.of(ins), W.inputs(w1),
    W.inputs(w2), e)

# LAW: a source of either kind judges a BEND_LIB tree as a clone weighed to
# the narHash it records
law lib_as_clone.src:
  for src: L.Src
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(src, W.Lib{}, hash, manifest, ss)
    == W.accept.src(src, W.Clone{L.src.nar(src)}, hash, manifest, ss)
    : W.Verdict}

def lib_as_clone.src(src, _hash, _manifest, _ss):
  match src:
    case L.Hub{}:
      {==}
    case L.Git{url, rev, entry, root, nar, tag}:
      {==}

def Laws.lib_judged_as_clone(orgs, hash, manifest, ss):
  lib_as_clone.src(L.origin(orgs, hash), hash, manifest, ss)

# LAW: how the bytes arrived, as a fresh clone would have it, is judged as it
# was, for a source of either kind
law reclone.how_judged:
  for src: L.Src
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(src, W.reclone.how(how, src), hash, manifest, ss)
    == W.accept.src(src, how, hash, manifest, ss) : W.Verdict}

def reclone.how_judged(src, how, hash, manifest, ss):
  match how:
    case W.Lib{}:
      Equal.sym(W.Verdict,
        W.accept.src(src, W.Lib{}, hash, manifest, ss),
        W.accept.src(src, W.Clone{L.src.nar(src)}, hash, manifest, ss),
        lib_as_clone.src(src, hash, manifest, ss))
    case W.Clone{got}:
      {==}
    case W.Served{}:
      {==}

# LAW: one answer, as a fresh clone would have it, is judged as it was
law reclone.one_judged:
  for +orgs: List<&2, L.Origin>
  for +hash: String
  for a: W.Answer
  {W.accept(orgs, hash, W.reclone.one(orgs, hash, a))
    == W.accept(orgs, hash, a) : W.Verdict}

def reclone.one_judged(orgs, hash, a):
  match a:
    case W.Miss{why}:
      {==}
    case W.Got{how, manifest, ss}:
      reclone.how_judged(L.origin(orgs, hash), how, hash, manifest, ss)

# LAW: every answer, as a fresh clone would have it, is judged as it was
law reclone_judged:
  for +orgs: List<&2, L.Origin>
  for rs: List<&2, W.Reply>
  {W.judge(orgs, W.reclone(orgs, rs)) == W.judge(orgs, rs)
    : List<&2, W.Judged>}

def reclone_judged(orgs, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+hash, a} <> t:
      Equal.trans(List<&2, W.Judged>,
        W.Judged{hash, W.accept(orgs, hash, W.reclone.one(orgs, hash, a))}
          <> W.judge(orgs, W.reclone(orgs, t)),
        W.Judged{hash, W.accept(orgs, hash, a)}
          <> W.judge(orgs, W.reclone(orgs, t)),
        W.Judged{hash, W.accept(orgs, hash, a)} <> W.judge(orgs, t),
        Equal.cong(W.Verdict, List<&2, W.Judged>,
          v => W.Judged{hash, v} <> W.judge(orgs, W.reclone(orgs, t)),
          W.accept(orgs, hash, W.reclone.one(orgs, hash, a)),
          W.accept(orgs, hash, a),
          reclone.one_judged(orgs, hash, a)),
        Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
          js => W.Judged{hash, W.accept(orgs, hash, a)} <> js,
          W.judge(orgs, W.reclone(orgs, t)),
          W.judge(orgs, t),
          reclone_judged(orgs, t)))

# The lock document's first step. The lemmas are about lists of chars, since
# eztoml's trim and strip walk a string as one.

# LAW: a string's chars joined are the chars of the two joined
law to_list_append:
  for +a: String
  for +b: String
  {String.to_list(String.append(a, b))
    == List.append(&2, Char, String.to_list(a), String.to_list(b))
    : List<&2, Char>}

def to_list_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(List<&2, Char>, List<&2, Char>, cs => h <> cs,
        String.to_list(String.append(t, b)),
        List.append(&2, Char, String.to_list(t), String.to_list(b)),
        to_list_append(t, b))

# LAW: chars appended to a string's chars read back as the string and then
# them
law from_to_append:
  for +v: String
  for +ys: List<&2, Char>
  {String.from_list(List.append(&2, Char, String.to_list(v), ys))
    == String.append(v, String.from_list(ys)) : String}

def from_to_append(v, ys):
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, s => SCon{h, s},
        String.from_list(List.append(&2, Char, String.to_list(t), ys)),
        String.append(t, String.from_list(ys)),
        from_to_append(t, ys))

# LAW: a trim that has stopped skipping keeps every char, reversed onto what
# it kept already
law walk_kept:
  for +xs: List<&2, Char>
  for +acc: List<&2, Char>
  {T.trim.walk(xs, T.Trim{False{}, acc})
    == T.Trim{False{}, List.reverse.go(&2, Char, xs, acc)} : T.Trim}

def walk_kept(xs, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_kept(t, h <> acc)

# LAW: reversing onto an accumulator goes through an append one half at a time
law rev_append:
  for +xs: List<&2, Char>
  for +ys: List<&2, Char>
  for +acc: List<&2, Char>
  {List.reverse.go(&2, Char, List.append(&2, Char, xs, ys), acc)
    == List.reverse.go(&2, Char, ys, List.reverse.go(&2, Char, xs, acc))
    : List<&2, Char>}

def rev_append(xs, ys, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      rev_append(t, ys, h <> acc)

# LAW: reversing twice puts the first list back in front of the second
# accumulator
law rev_rev:
  for +xs: List<&2, Char>
  for +ys: List<&2, Char>
  for +zs: List<&2, Char>
  {List.reverse.go(&2, Char, List.reverse.go(&2, Char, xs, ys), zs)
    == List.reverse.go(&2, Char, ys, List.append(&2, Char, xs, zs))
    : List<&2, Char>}

def rev_rev(xs, ys, zs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      rev_rev(t, h <> ys, zs)

# LAW: the first pass over a quoted value
law trim_quoted.first:
  for +v: String
  {T.trim.pass(String.to_list(T.quote(v)))
    == '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"'])
    : List<&2, Char>}

def trim_quoted.first(v):
  Equal.trans(List<&2, Char>,
    T.trim.pass(String.to_list(T.quote(v))),
    List.reverse.go(&2, Char,
      List.append(&2, Char, String.to_list(v), ['"']), ['"']),
    '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"']),
    Equal.trans(List<&2, Char>,
      T.trim.pass(String.to_list(T.quote(v))),
      T.trim.out(T.trim.walk(
        List.append(&2, Char, String.to_list(v), ['"']),
        T.Trim{False{}, ['"']})),
      List.reverse.go(&2, Char,
        List.append(&2, Char, String.to_list(v), ['"']), ['"']),
      Equal.cong(List<&2, Char>, List<&2, Char>,
        cs => T.trim.out(T.trim.walk(cs, T.Trim{False{}, ['"']})),
        String.to_list(String.append(v, "\"")),
        List.append(&2, Char, String.to_list(v), ['"']),
        to_list_append(v, "\"")),
      Equal.cong(T.Trim, List<&2, Char>, st => T.trim.out(st),
        T.trim.walk(List.append(&2, Char, String.to_list(v), ['"']),
          T.Trim{False{}, ['"']}),
        T.Trim{False{}, List.reverse.go(&2, Char,
          List.append(&2, Char, String.to_list(v), ['"']), ['"'])},
        walk_kept(List.append(&2, Char, String.to_list(v), ['"']), ['"']))),
    rev_append(String.to_list(v), ['"'], ['"']))

# LAW: the two passes of a trim over a quoted value, as reversals
law trim_quoted.passes:
  for +v: String
  {T.trim(T.quote(v))
    == String.from_list(List.reverse.go(&2, Char,
      List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])) : String}

def trim_quoted.passes(v):
  Equal.trans(String,
    T.trim(T.quote(v)),
    String.from_list(T.trim.pass(
      '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"']))),
    String.from_list(List.reverse.go(&2, Char,
      List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])),
    Equal.cong(List<&2, Char>, String,
      cs => String.from_list(T.trim.pass(cs)),
      T.trim.pass(String.to_list(T.quote(v))),
      '"' <> List.reverse.go(&2, Char, String.to_list(v), ['"']),
      trim_quoted.first(v)),
    Equal.cong(T.Trim, String, st => String.from_list(T.trim.out(st)),
      T.trim.walk(List.reverse.go(&2, Char, String.to_list(v), ['"']),
        T.Trim{False{}, ['"']}),
      T.Trim{False{}, List.reverse.go(&2, Char,
        List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])},
      walk_kept(List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])))

# The trim of a quoted value, one pass at a time. The first pass keeps the
# opening quote and so everything after it, reversed; the second keeps the
# closing quote, now first, and reverses the rest back.
def Laws.trim_quoted(v):
  Equal.trans(String,
    T.trim(T.quote(v)),
    String.from_list(List.reverse.go(&2, Char,
      List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])),
    T.quote(v),
    trim_quoted.passes(v),
    Equal.trans(String,
      String.from_list(List.reverse.go(&2, Char,
        List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"'])),
      String.from_list('"' <> List.append(&2, Char, String.to_list(v), ['"'])),
      T.quote(v),
      Equal.cong(List<&2, Char>, String, cs => String.from_list(cs),
        List.reverse.go(&2, Char,
          List.reverse.go(&2, Char, String.to_list(v), ['"']), ['"']),
        '"' <> List.append(&2, Char, String.to_list(v), ['"']),
        rev_rev(String.to_list(v), ['"'], ['"'])),
      Equal.cong(String, String, s => SCon{'"', s},
        String.from_list(List.append(&2, Char, String.to_list(v), ['"'])),
        String.append(v, "\""),
        from_to_append(v, ['"']))))

# LAW: the walk that drops a trailing quote, one char behind the list it
# walks
law back_go_quote:
  for +t: List<&2, Char>
  for +h: Char
  {T.strip.back.go(List.append(&2, Char, t, ['"']), h, '"') == h <> t
    : List<&2, Char>}

def back_go_quote(t, h):
  match t:
    case []:
      {==}
    case +h2 <> +t2:
      Equal.cong(List<&2, Char>, List<&2, Char>, cs => h <> cs,
        T.strip.back.go(List.append(&2, Char, t2, ['"']), h2, '"'),
        h2 <> t2,
        back_go_quote(t2, h2))

# LAW: a list that ends in a quote, with the quote dropped
law back_quote:
  for +xs: List<&2, Char>
  {T.strip.back(List.append(&2, Char, xs, ['"']), '"') == xs
    : List<&2, Char>}

def back_quote(xs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      back_go_quote(t, h)

# LAW: a string's chars read back as the string
law from_to:
  for +v: String
  {String.from_list(String.to_list(v)) == v : String}

def from_to(v):
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, s => SCon{h, s},
        String.from_list(String.to_list(t)), t, from_to(t))

def Laws.strip_quoted(v):
  Equal.trans(String,
    T.strip(T.quote(v), '"', '"'),
    String.from_list(T.strip.back(
      List.append(&2, Char, String.to_list(v), ['"']), '"')),
    v,
    Equal.cong(List<&2, Char>, String,
      cs => String.from_list(T.strip.back(cs, '"')),
      String.to_list(String.append(v, "\"")),
      List.append(&2, Char, String.to_list(v), ['"']),
      to_list_append(v, "\"")),
    Equal.trans(String,
      String.from_list(T.strip.back(
        List.append(&2, Char, String.to_list(v), ['"']), '"')),
      String.from_list(String.to_list(v)),
      v,
      Equal.cong(List<&2, Char>, String, cs => String.from_list(cs),
        T.strip.back(List.append(&2, Char, String.to_list(v), ['"']), '"'),
        String.to_list(v),
        back_quote(String.to_list(v))),
      from_to(v)))

def Laws.clone_reproduces(ledger, listing, rs):
  Equal.cong(List<&2, W.Judged>, W.Outcome,
    js => W.plan.of(W.Inputs{ledger, listing, js}),
    W.judge(W.origins(ledger), W.reclone(W.origins(ledger), rs)),
    W.judge(W.origins(ledger), rs),
    reclone_judged(W.origins(ledger), rs))

# The cut at `=`. The reader's split compares each char with the separator,
# so a char it cut at has to be shown to be the separator, and Base states no
# such fact: a char is a 32-bit word, and two words that compare equal are one
# word by induction on the width.

# the type that is empty exactly where a comparison answered EQ
def cmp.emp(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

def cmp.lt(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : cmp.emp(_)
  Unit{}

def cmp.gt(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : cmp.emp(_)
  Unit{}

# LAW: a comparison that reads as equal is EQ
law cmp_is_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def cmp_is_eq(c, e):
  match c:
    case LT{}:
      Eq.bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
    case EQ{}:
      {==}
    case GT{}:
      Eq.bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)

# LAW: two bits that compare equal are one bit
law bool_eq:
  for a: Bool
  for b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

def bool_eq(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Eq.bit.gone(&2, {False{} == True{} : Bool}, cmp.lt(e))
    case True{} False{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, cmp.gt(e))
    case True{} True{}:
      {==}

# LAW: a word comparison that ends EQ had tails that compared EQ
law fin_tail:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

def fin_tail(_ab, _bb, t, e):
  match t:
    case LT{}:
      Eq.bit.gone(&2, {LT{} == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      {==}
    case GT{}:
      Eq.bit.gone(&2, {GT{} == EQ{} : Cmp}, cmp.gt(e))

# LAW: and heads that compared EQ
law fin_head:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {Bool.cmp(ab, bb) == EQ{} : Cmp}

def fin_head(ab, bb, t, e):
  match t:
    case LT{}:
      Eq.bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      e
    case GT{}:
      Eq.bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.gt(e))

# LAW: two words that compare equal are one word
law word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(Word(1n+p), WCon{ab, at}, WCon{bb, at}, WCon{bb, bt},
            Equal.cong(Bool, Word(1n+p), x => WCon{x, at}, ab, bb,
              bool_eq(ab, bb, fin_head(ab, bb, Word.cmp(p, at, bt), e))),
            Equal.cong(Word(p), Word(1n+p), y => WCon{bb, y}, at, bt,
              word_eq(p, at, bt, fin_tail(ab, bb, Word.cmp(p, at, bt), e))))

# LAW: two code points that compare equal are one char
law u32_eq:
  for x: U32
  for y: U32
  for e: {U32.is_eq(x, y) == True{} : Bool}
  {Chr{x} == Chr{y} : Char}

def u32_eq(x, y, e):
  match x y:
    case U32{+wx} U32{+wy}:
      Equal.cong(Word(32n), Char, w => Chr{U32{w}}, wx, wy,
        word_eq(32n, wx, wy, cmp_is_eq(Word.cmp(32n, wx, wy), e)))

# LAW: two chars that compare equal are one char
law char_eq_true:
  for a: Char
  for b: Char
  for e: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

def char_eq_true(a, b, e):
  match a b:
    case Chr{x} Chr{y}:
      u32_eq(x, y, e)

# LAW: one step of a split always leaves at least one piece
law fin_cons:
  for h: Char
  for r: List<&2, String>
  for b: Bool
  {List.is_empty(&2, String, String.split.fin(h, r, b)) == False{} : Bool}

# LAW: a char pushed onto the pieces leaves at least one
law push_cons:
  for h: Char
  for r: List<&2, String>
  {List.is_empty(&2, String, String.split.push(h, r)) == False{} : Bool}

def push_cons(_h, r):
  match r:
    case []:
      {==}
    case y <> ys:
      {==}

def fin_cons(h, r, b):
  match b:
    case False{}:
      push_cons(h, r)
    case True{}:
      {==}

# LAW: and so does a whole split
law split_cons:
  for s: String
  for +c: Char
  {List.is_empty(&2, String, String.split(s, c)) == False{} : Bool}

def split_cons(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      fin_cons(h, String.split(t, c), Char.is_eq(h, c))

# LAW: a join that starts from a piece with a char in front has the char in
# front
law join_go_cons:
  for ys: List<&2, String>
  for y: String
  for h: Char
  for +sep: String
  {String.join.go(ys, SCon{h, y}, sep) == SCon{h, String.join.go(ys, y, sep)}
    : String}

def join_go_cons(ys, _y, _h, _sep):
  match ys:
    case []:
      {==}
    case y2 <> t:
      {==}

# LAW: one char of the split joined back, once the rest is known to have a
# first piece, with which way the comparison went given as a parameter
law join_split.cons:
  for +h: Char
  for +t: String
  for +c: Char
  for +y: String
  for +ys: List<&2, String>
  for b: Bool
  for eb: {Char.is_eq(h, c) == b : Bool}
  for ih: {String.join.go(ys, y, SCon{c, SNil{}}) == t : String}
  {String.join(String.split.fin(h, y <> ys, b), SCon{c, SNil{}}) == SCon{h, t}
    : String}

def join_split.cons(h, t, c, y, ys, b, eb, ih):
  match b:
    case False{}:
      Equal.trans(String,
        String.join.go(ys, SCon{h, y}, SCon{c, SNil{}}),
        SCon{h, String.join.go(ys, y, SCon{c, SNil{}})},
        SCon{h, t},
        join_go_cons(ys, y, h, SCon{c, SNil{}}),
        Equal.cong(String, String, x => SCon{h, x},
          String.join.go(ys, y, SCon{c, SNil{}}), t, ih))
    case True{}:
      Equal.trans(String,
        SCon{c, String.join.go(ys, y, SCon{c, SNil{}})},
        SCon{c, t},
        SCon{h, t},
        Equal.cong(String, String, x => SCon{c, x},
          String.join.go(ys, y, SCon{c, SNil{}}), t, ih),
        Equal.cong(Char, String, x => SCon{x, t}, c, h,
          Equal.sym(Char, h, c, char_eq_true(h, c, eb))))

# LAW: one char of the split, joined back, with which way the comparison went
# and the pieces of the rest given as parameters
law join_split.arm:
  for +h: Char
  for +t: String
  for +c: Char
  for r: List<&2, String>
  for b: Bool
  for eb: {Char.is_eq(h, c) == b : Bool}
  for er: {List.is_empty(&2, String, r) == False{} : Bool}
  for ih: {String.join(r, SCon{c, SNil{}}) == t : String}
  {String.join(String.split.fin(h, r, b), SCon{c, SNil{}}) == SCon{h, t}
    : String}

def join_split.arm(h, t, c, r, b, eb, er, ih):
  match r:
    case []:
      Eq.bit.absurd2(&2, {String.join(String.split.fin(h, [], b),
        SCon{c, SNil{}}) == SCon{h, t} : String}, er)
    case +y <> +ys:
      join_split.cons(h, t, c, y, ys, b, eb, ih)

def Laws.join_split(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      join_split.arm(h, t, c, String.split(t, c), Char.is_eq(h, c), {==},
        split_cons(t, c), Laws.join_split(t, c))
