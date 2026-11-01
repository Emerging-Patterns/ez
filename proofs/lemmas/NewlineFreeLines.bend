# lines that hold no newline, written out as a file and read back
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/ignore.bend as I
import ../../src/add/world.bend as A
import ./PlanEffectFacts.bend as M1

# The allowlist. Both laws are proved the same way: the walk is taken apart
# one line at a time, each line's kind is lifted into a parameter so the
# walk can reduce on it, and what the walk puts in a line's place is shown
# to add nothing to the side being counted. `hashes` counts the allowlist,
# `others` the project's lines.

# LAW: nothing appended to a list of lines leaves it
law lines_app_nil:
  for xs: List<&2, String>
  {List.append(&2, String, xs, []) == xs : List<&2, String>}

def lines_app_nil(xs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        List.append(&2, String, t, []), t, lines_app_nil(t))

# LAW: the line ez writes for a hash reads back as that hash's allowlist
# line. An empty hash would read back as the library directory, which is
# why neither `vended` nor `allows` ever takes one.
law kind_allow:
  for +x: String
  for e: {String.is_empty(x) == False{} : Bool}
  {I.kind(I.allow(x)) == I.Allow{x} : I.Rule}

def kind_allow(x, e):
  match x:
    case SNil{}:
      Eq.bit.absurd2(&2, {I.kind(I.allow(SNil{})) == I.Allow{SNil{}} : I.Rule}, e)
    case SCon{c, t}:
      {==}

# whether every hash of a list names something. Law vocabulary: ez never
# calls it.
def full.all(hs: List<&2, String>) -> Bool:
  match hs:
    case []:
      True{}
    case h <> t:
      +rest = full.all(t)
      Bool.and(Bool.not(String.is_empty(h)), rest)

# LAW: the left half of an `or` that answered False
law or_left_ledger:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_left_ledger(a, _b, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: a hash of a list whose hashes all name something is not empty
law full_head:
  for +h: String
  for t: List<&2, String>
  for e: {full.all(h <> t) == True{} : Bool}
  {String.is_empty(h) == False{} : Bool}

def full_head(h, t, e):
  Eq.not.true(String.is_empty(h),
    Eq.and.left(Bool.not(String.is_empty(h)), full.all(t), e))

# LAW: and neither is any hash after it
law full_tail:
  for +h: String
  for t: List<&2, String>
  for e: {full.all(h <> t) == True{} : Bool}
  {full.all(t) == True{} : Bool}

def full_tail(h, t, e):
  Eq.and.right(Bool.not(String.is_empty(h)), full.all(t), e)

# LAW: one hash of the walk that keeps each once, with whether it is passed
# over given as a parameter. A kept hash is not empty.
law once_full.arm:
  for +h: String
  for t: List<&2, String>
  for +seen: List<&2, String>
  for skip: Bool
  for es: {Bool.or(String.is_empty(h), I.named(seen, h)) == skip : Bool}
  for ih: {full.all(I.once.go(t, I.once.seen(skip, h, seen))) == True{} : Bool}
  {full.all(I.once.put(skip, h, I.once.go(t, I.once.seen(skip, h, seen))))
    == True{} : Bool}

def once_full.arm(h, t, seen, skip, es, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.is_empty(h), False{},
        or_left_ledger(String.is_empty(h), I.named(seen, h), es))
        : {Bool.and(Bool.not(_), full.all(I.once.go(t, h <> seen))) == True{} : Bool}
      ih

# LAW: every hash the walk keeps names something
law once_full:
  for hs: List<&2, String>
  for +seen: List<&2, String>
  {full.all(I.once.go(hs, seen)) == True{} : Bool}

def once_full(hs, seen):
  match hs:
    case []:
      {==}
    case +h <> +t:
      once_full.arm(h, t, seen, Bool.or(String.is_empty(h), I.named(seen, h)), {==},
        once_full(t, I.once.seen(Bool.or(String.is_empty(h), I.named(seen, h)), h, seen)))

# LAW: so every hash a ledger vends names something
law vended_full:
  for ds: List<&2, M.Dep>
  {full.all(I.vended(ds)) == True{} : Bool}

def vended_full(ds):
  once_full(I.vendors(ds), [])

# LAW: lines written out as a file and cut at the newline are those lines and
# the empty piece after the last newline
law file_text_split:
  for +ls: List<&2, String>
  for +e: {Str.clear.all(ls, '\n') == True{} : Bool}
  {String.split(I.file.text(ls), '\n') == List.append(&2, String, ls, [""])
    : List<&2, String>}

def file_text_split(ls, e):
  match ls:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        String.split(String.append(h, SCon{'\n', I.file.text(t)}), '\n'),
        String.append(h, SNil{}) <> String.split(I.file.text(t), '\n'),
        h <> List.append(&2, String, t, [""]),
        Str.split_front(h, SCon{'\n', I.file.text(t)}, '\n', SNil{},
          String.split(I.file.text(t), '\n'),
          Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), e),
          Str.split_sep('\n', I.file.text(t))),
        Equal.trans(List<&2, String>,
          String.append(h, SNil{}) <> String.split(I.file.text(t), '\n'),
          h <> String.split(I.file.text(t), '\n'),
          h <> List.append(&2, String, t, [""]),
          Equal.cong(String, List<&2, String>,
            x => x <> String.split(I.file.text(t), '\n'),
            String.append(h, SNil{}), h, Str.append_nil(h)),
          Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
            String.split(I.file.text(t), '\n'), List.append(&2, String, t, [""]),
            file_text_split(t, Eq.and.right(Str.clear(h, '\n'),
              Str.clear.all(t, '\n'), e)))))

# LAW: the empty piece after the last newline is dropped, and nothing else
law unend_go_app:
  for t: List<&2, String>
  for +h: String
  {I.unend.go(List.append(&2, String, t, [""]), h) == h <> t : List<&2, String>}

def unend_go_app(t, h):
  match t:
    case []:
      {==}
    case +h2 <> +t2:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.unend.go(List.append(&2, String, t2, [""]), h2), h2 <> t2,
        unend_go_app(t2, h2))

# LAW: and so a file of lines reads back as its lines
law unend_app:
  for ls: List<&2, String>
  {I.unend(List.append(&2, String, ls, [""])) == ls : List<&2, String>}

def unend_app(ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      unend_go_app(t, h)

# LAW: lines that hold no newline, written out as a file, read back as those
# lines
law file_lines_text:
  for +ls: List<&2, String>
  for +e: {Str.clear.all(ls, '\n') == True{} : Bool}
  {I.file.lines(I.file.text(ls)) == ls : List<&2, String>}

def file_lines_text(ls, e):
  Equal.trans(List<&2, String>,
    I.unend(String.split(I.file.text(ls), '\n')),
    I.unend(List.append(&2, String, ls, [""])),
    ls,
    Equal.cong(List<&2, String>, List<&2, String>, y => I.unend(y),
      String.split(I.file.text(ls), '\n'), List.append(&2, String, ls, [""]),
      file_text_split(ls, e)),
    unend_app(ls))

# LAW: dropping the last piece when it is empty leaves no line with a newline
law unend_go_clear:
  for t: List<&2, String>
  for +h: String
  for +e: {Str.clear.all(h <> t, '\n') == True{} : Bool}
  {Str.clear.all(I.unend.go(t, h), '\n') == True{} : Bool}

def unend_go_clear(t, h, e):
  match t:
    case []:
      match h:
        case SNil{}:
          {==}
        case SCon{c, r}:
          e
    case +h2 <> +t2:
      M1.and_tt(Str.clear(h, '\n'), Str.clear.all(I.unend.go(t2, h2), '\n'),
        Eq.and.left(Str.clear(h, '\n'), Str.clear.all(h2 <> t2, '\n'), e),
        unend_go_clear(t2, h2,
          Eq.and.right(Str.clear(h, '\n'), Str.clear.all(h2 <> t2, '\n'), e)))

# LAW: and neither does any piece that is kept
law unend_clear:
  for ps: List<&2, String>
  for +e: {Str.clear.all(ps, '\n') == True{} : Bool}
  {Str.clear.all(I.unend(ps), '\n') == True{} : Bool}

def unend_clear(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      unend_go_clear(t, h, e)

# LAW: no line of a file holds a newline
law file_lines_clear:
  for +text: String
  {Str.clear.all(I.file.lines(text), '\n') == True{} : Bool}

def file_lines_clear(text):
  unend_clear(String.split(text, '\n'), Str.split_clear(text, '\n'))

# LAW: two runs of lines hold no newline exactly when neither does
law clear_all_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {Str.clear.all(List.append(&2, String, xs, ys), '\n')
    == Bool.and(Str.clear.all(xs, '\n'), Str.clear.all(ys, '\n')) : Bool}

def clear_all_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, Str.clear.all(List.append(&2, String, t, ys), '\n'),
        Bool.and(Str.clear.all(t, '\n'), Str.clear.all(ys, '\n')),
        clear_all_app(t, ys))
        : {Bool.and(Str.clear(h, '\n'), _)
          == Bool.and(Bool.and(Str.clear(h, '\n'), Str.clear.all(t, '\n')),
            Str.clear.all(ys, '\n')) : Bool}
      Str.and_assoc(Str.clear(h, '\n'), Str.clear.all(t, '\n'),
        Str.clear.all(ys, '\n'))

# LAW: two runs of lines that hold no newline hold none together
law clear_app:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for ex: {Str.clear.all(xs, '\n') == True{} : Bool}
  for ey: {Str.clear.all(ys, '\n') == True{} : Bool}
  {Str.clear.all(List.append(&2, String, xs, ys), '\n') == True{} : Bool}

def clear_app(xs, ys, ex, ey):
  Equal.trans(Bool,
    Str.clear.all(List.append(&2, String, xs, ys), '\n'),
    Bool.and(Str.clear.all(xs, '\n'), Str.clear.all(ys, '\n')),
    True{},
    clear_all_app(xs, ys),
    M1.and_tt(Str.clear.all(xs, '\n'), Str.clear.all(ys, '\n'), ex, ey))

# LAW: the block, put down or not, holds no newline when it holds none
law placed_clear:
  for +d: Bool
  for +blk: List<&2, String>
  for eb: {Str.clear.all(blk, '\n') == True{} : Bool}
  {Str.clear.all(I.placed(d, blk), '\n') == True{} : Bool}

def placed_clear(d, _blk, eb):
  match d:
    case True{}:
      {==}
    case False{}:
      eb

# LAW: one line of the walk, with its kind given as a parameter: what the
# walk puts in its place holds no newline
law walk_clear.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +eh: {Str.clear(h, '\n') == True{} : Bool}
  for +ef: {Str.clear.all(fix, '\n') == True{} : Bool}
  for +eb: {Str.clear.all(blk, '\n') == True{} : Bool}
  for ihd: {Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n') == True{} : Bool}
  for iht: {Str.clear.all(I.walk(I.tag(t), fix, blk, True{}), '\n') == True{} : Bool}
  {Str.clear.all(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d), '\n') == True{} : Bool}

def walk_clear.arm(k, h, t, fix, blk, d, eh, ef, eb, ihd, iht):
  match k:
    case I.Other{}:
      M1.and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Star{}:
      M1.and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Lib{}:
      M1.and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Pkgs{}:
      M1.and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Dir{}:
      clear_app(fix, I.walk(I.tag(t), fix, blk, d), ef, ihd)
    case I.Allow{x}:
      clear_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}),
        placed_clear(d, blk, eb), iht)

# LAW: every line the walk writes is a line of the file, a rule or the block,
# so it holds no newline when none of those does
law walk_clear:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +er: {Str.clear.all(raw, '\n') == True{} : Bool}
  for +ef: {Str.clear.all(fix, '\n') == True{} : Bool}
  for +eb: {Str.clear.all(blk, '\n') == True{} : Bool}
  {Str.clear.all(I.walk(I.tag(raw), fix, blk, d), '\n') == True{} : Bool}

def walk_clear(raw, fix, blk, d, er, ef, eb):
  match raw:
    case []:
      placed_clear(d, blk, eb)
    case +h <> +t:
      walk_clear.arm(I.kind(h), h, t, fix, blk, d,
        Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), er), ef, eb,
        walk_clear(t, fix, blk, d,
          Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), er), ef, eb),
        walk_clear(t, fix, blk, True{},
          Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), er), ef, eb))

# LAW: the three rules hold no newline, whichever of them are written
law rules_clear:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {Str.clear.all(I.rules.go(b1, b2, b3), '\n') == True{} : Bool}

def rules_clear(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: the rules, written or not, hold no newline
law need_clear:
  for s: Bool
  for +rs: List<&2, String>
  for h: {Str.clear.all(rs, '\n') == True{} : Bool}
  {Str.clear.all(I.need(s, rs), '\n') == True{} : Bool}

def need_clear(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: the lines ez writes for hashes that hold no newline hold none
law each_clear:
  for +hs: List<&2, String>
  for +e: {Str.clear.all(hs, '\n') == True{} : Bool}
  {Str.clear.all(I.allow.each(hs), '\n') == True{} : Bool}

def each_clear(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      M1.and_tt(Str.clear(I.allow(h), '\n'), Str.clear.all(I.allow.each(t), '\n'),
        Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), e),
        each_clear(t, Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), e)))

# LAW: the block holds no newline when no vendored hash does
law block_clear:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, I.Line>
  for +e: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {Str.clear.all(I.block(ds, ls), '\n') == True{} : Bool}

def block_clear(ds, ls, e):
  clear_app(
    I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
      I.rules(ls)),
    I.allows(ds),
    need_clear(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
      I.rules(ls),
      rules_clear(I.has(ls, I.Star{}), I.has(ls, I.Lib{}), I.has(ls, I.Pkgs{}))),
    each_clear(I.vended(ds), e))

# LAW: no line of the allowlist `I.lines` makes holds a newline, when no line
# of the file and no vendored hash does
law lines_clear:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  for +el: {Str.clear.all(ls, '\n') == True{} : Bool}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {Str.clear.all(I.lines(ds, ls), '\n') == True{} : Bool}

def lines_clear(ds, ls, el, ev):
  walk_clear(ls, I.rules(I.tag(ls)), I.block(ds, I.tag(ls)), False{}, el,
    rules_clear(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
      I.has(I.tag(ls), I.Pkgs{})),
    block_clear(ds, I.tag(ls), ev))
