# which lines are allowlist lines, and what the walk over .gitignore puts down
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/ignore.bend as I
import ../../src/add/world.bend as A
import ../../laws/GitignoreAllowlistIsLedger.bend as L1
import ./LockPlannerFacts.bend as M1
import ./NewlineFreeLines.bend as M2
import ./PlanEffectFacts.bend as M3

# whether the walk keeps every line of a list as it is
def kept.all(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case +h <> t:
      +rest = kept.all(t)
      Bool.and(M1.keeps(I.kind(h)), rest)

# whether a kind of line is an allowlist line
def allowed(k: I.Rule) -> Bool:
  match k:
    case I.Other{}:
      False{}
    case I.Dir{}:
      False{}
    case I.Star{}:
      False{}
    case I.Lib{}:
      False{}
    case I.Pkgs{}:
      False{}
    case I.Allow{_h}:
      True{}

# whether every line of a list is an allowlist line
def allowed.all(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case +h <> t:
      +rest = allowed.all(t)
      Bool.and(allowed(I.kind(h)), rest)

# LAW: where the brackets fall in a run of lines does not change the run
law lines_assoc:
  for a: List<&2, String>
  for +b: List<&2, String>
  for +c: List<&2, String>
  {List.append(&2, String, List.append(&2, String, a, b), c)
    == List.append(&2, String, a, List.append(&2, String, b, c)) : List<&2, String>}

def lines_assoc(a, b, c):
  match a:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        List.append(&2, String, List.append(&2, String, t, b), c),
        List.append(&2, String, t, List.append(&2, String, b, c)),
        lines_assoc(t, b, c))

# LAW: two runs are kept exactly when each is
law kept_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {kept.all(List.append(&2, String, xs, ys))
    == Bool.and(kept.all(xs), kept.all(ys)) : Bool}

def kept_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, kept.all(List.append(&2, String, t, ys)),
        Bool.and(kept.all(t), kept.all(ys)), kept_app(t, ys))
        : {Bool.and(M1.keeps(I.kind(h)), _)
          == Bool.and(Bool.and(M1.keeps(I.kind(h)), kept.all(t)), kept.all(ys)) : Bool}
      Str.and_assoc(M1.keeps(I.kind(h)), kept.all(t), kept.all(ys))

# LAW: and so two kept runs are kept together
law kept_both:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for ex: {kept.all(xs) == True{} : Bool}
  for ey: {kept.all(ys) == True{} : Bool}
  {kept.all(List.append(&2, String, xs, ys)) == True{} : Bool}

def kept_both(xs, ys, ex, ey):
  Equal.trans(Bool, kept.all(List.append(&2, String, xs, ys)),
    Bool.and(kept.all(xs), kept.all(ys)), True{},
    kept_app(xs, ys), M3.and_tt(kept.all(xs), kept.all(ys), ex, ey))

# LAW: one line of a kept run, with its kind given as a parameter: it is
# kept, in front of the rest
law walk_kept.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for e: {M1.keeps(k) == True{} : Bool}
  for ih: {I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d)
    == List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)) : List<&2, String>}
  {I.walk(I.Line{k, h} <> I.tag(List.append(&2, String, t, z)), fix, blk, d)
    == h <> List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)) : List<&2, String>}

def walk_kept.arm(k, h, t, z, fix, blk, d, e, ih):
  match k:
    case I.Other{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Star{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Lib{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Pkgs{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Dir{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, d) == h <> List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d))
        : List<&2, String>}, e)
    case I.Allow{x}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Allow{x}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, d) == h <> List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d))
        : List<&2, String>}, e)

# LAW: a run of lines the walk keeps as they are comes out as it went in,
# whatever follows it
law walk_kept:
  for +xs: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +e: {kept.all(xs) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, xs, z)), fix, blk, d)
    == List.append(&2, String, xs, I.walk(I.tag(z), fix, blk, d)) : List<&2, String>}

def walk_kept(xs, z, fix, blk, d, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_kept.arm(I.kind(h), h, t, z, fix, blk, d,
        Eq.and.left(M1.keeps(I.kind(h)), kept.all(t), e),
        walk_kept(t, z, fix, blk, d, Eq.and.right(M1.keeps(I.kind(h)), kept.all(t), e)))

# LAW: a kept run, all of it, is itself and then the block, if still owed
law walk_clean:
  for +xs: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +e: {kept.all(xs) == True{} : Bool}
  {I.walk(I.tag(xs), fix, blk, d) == List.append(&2, String, xs, I.placed(d, blk))
    : List<&2, String>}

def walk_clean(xs, fix, blk, d, e):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(xs), fix, blk, d),
    I.walk(I.tag(List.append(&2, String, xs, [])), fix, blk, d),
    List.append(&2, String, xs, I.placed(d, blk)),
    Equal.cong(List<&2, String>, List<&2, String>, y => I.walk(I.tag(y), fix, blk, d),
      xs, List.append(&2, String, xs, []),
      Equal.sym(List<&2, String>, List.append(&2, String, xs, []), xs, M2.lines_app_nil(xs))),
    walk_kept(xs, [], fix, blk, d, e))

# LAW: one allowlist line, once the block is down, with its kind given as a
# parameter: it is dropped
law walk_drop.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for e: {allowed(k) == True{} : Bool}
  for ih: {I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, True{})
    == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}
  {I.walk(I.Line{k, h} <> I.tag(List.append(&2, String, t, z)), fix, blk, True{})
    == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}

def walk_drop.arm(k, h, t, z, fix, blk, e, ih):
  match k:
    case I.Allow{x}:
      ih
    case I.Other{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Other{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Dir{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Star{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Star{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Lib{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Lib{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Pkgs{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Pkgs{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)

# LAW: a run of allowlist lines, once the block is down, is dropped
law walk_drop:
  for +xs: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {allowed.all(xs) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, xs, z)), fix, blk, True{})
    == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}

def walk_drop(xs, z, fix, blk, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_drop.arm(I.kind(h), h, t, z, fix, blk,
        Eq.and.left(allowed(I.kind(h)), allowed.all(t), e),
        walk_drop(t, z, fix, blk, Eq.and.right(allowed(I.kind(h)), allowed.all(t), e)))

# LAW: the first allowlist line of a run of them, with its kind given as a
# parameter: the block goes down in its place, and the rest are dropped
law first_allow.arm:
  for k: I.Rule
  for +a1: String
  for +as: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for e: {allowed(k) == True{} : Bool}
  for +ea: {allowed.all(as) == True{} : Bool}
  {I.walk(I.Line{k, a1} <> I.tag(List.append(&2, String, as, z)), fix, blk, False{})
    == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{})) : List<&2, String>}

def first_allow.arm(k, a1, as, z, fix, blk, e, ea):
  match k:
    case I.Allow{x}:
      Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, blk, y),
        I.walk(I.tag(List.append(&2, String, as, z)), fix, blk, True{}),
        I.walk(I.tag(z), fix, blk, True{}),
        walk_drop(as, z, fix, blk, ea))
    case I.Other{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Other{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Dir{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Star{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Star{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Lib{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Lib{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Pkgs{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Pkgs{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)

# LAW: a run of allowlist lines, before the block is down: the block goes
# down in their place
law first_allow:
  for +a1: String
  for +as: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {allowed.all(a1 <> as) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, a1 <> as, z)), fix, blk, False{})
    == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{})) : List<&2, String>}

def first_allow(a1, as, z, fix, blk, e):
  first_allow.arm(I.kind(a1), a1, as, z, fix, blk,
    Eq.and.left(allowed(I.kind(a1)), allowed.all(as), e),
    Eq.and.right(allowed(I.kind(a1)), allowed.all(as), e))

# LAW: one line of the walk, with its kind given as a parameter: what it puts
# in the line's place is kept as it is, when the rules are and the block is
# already down
law walk_kept_out.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +ef: {kept.all(fix) == True{} : Bool}
  for +ep: {kept.all(I.placed(d, blk)) == True{} : Bool}
  for ihd: {kept.all(I.walk(I.tag(t), fix, blk, d)) == True{} : Bool}
  for iht: {kept.all(I.walk(I.tag(t), fix, blk, True{})) == True{} : Bool}
  {kept.all(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)) == True{} : Bool}

def walk_kept_out.arm(k, h, t, fix, blk, d, ek, ef, ep, ihd, iht):
  match k:
    case I.Other{}:
      %Equal.sym(I.Rule, I.kind(h), I.Other{}, ek)
        : {Bool.and(M1.keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Star{}:
      %Equal.sym(I.Rule, I.kind(h), I.Star{}, ek)
        : {Bool.and(M1.keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Lib{}:
      %Equal.sym(I.Rule, I.kind(h), I.Lib{}, ek)
        : {Bool.and(M1.keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Pkgs{}:
      %Equal.sym(I.Rule, I.kind(h), I.Pkgs{}, ek)
        : {Bool.and(M1.keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Dir{}:
      kept_both(fix, I.walk(I.tag(t), fix, blk, d), ef, ihd)
    case I.Allow{x}:
      kept_both(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), ep, iht)

# LAW: what the walk writes is kept as it is, when the rules are and the
# block, if it still goes down, is too
law walk_kept_out:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +ef: {kept.all(fix) == True{} : Bool}
  for +ep: {kept.all(I.placed(d, blk)) == True{} : Bool}
  {kept.all(I.walk(I.tag(raw), fix, blk, d)) == True{} : Bool}

def walk_kept_out(raw, fix, blk, d, ef, ep):
  match raw:
    case []:
      ep
    case +h <> +t:
      walk_kept_out.arm(I.kind(h), h, t, fix, blk, d, {==}, ef, ep,
        walk_kept_out(t, fix, blk, d, ef, ep),
        walk_kept_out(t, fix, blk, True{}, ef, {==}))

# LAW: an empty block, put down or not, is nothing
law placed_nil:
  for +d: Bool
  {I.placed(d, []) == [] : List<&2, String>}

def placed_nil(d):
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the second run over what the first wrote, once the block is down or
# holds nothing: every line is kept, and nothing is added
law idem_nil:
  for +raw: List<&2, String>
  for +fix: List<&2, String>
  for +fix2: List<&2, String>
  for +d: Bool
  for +d2: Bool
  for +ef: {kept.all(fix) == True{} : Bool}
  {I.walk(I.tag(I.walk(I.tag(raw), fix, [], d)), fix2, [], d2)
    == I.walk(I.tag(raw), fix, [], d) : List<&2, String>}

def idem_nil(raw, fix, fix2, d, d2, ef):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(I.walk(I.tag(raw), fix, [], d)), fix2, [], d2),
    List.append(&2, String, I.walk(I.tag(raw), fix, [], d), I.placed(d2, [])),
    I.walk(I.tag(raw), fix, [], d),
    walk_clean(I.walk(I.tag(raw), fix, [], d), fix2, [], d2,
      walk_kept_out(raw, fix, [], d, ef,
        Equal.cong(List<&2, String>, Bool, y => kept.all(y), I.placed(d, []), [],
          placed_nil(d)))),
    Equal.trans(List<&2, String>,
      List.append(&2, String, I.walk(I.tag(raw), fix, [], d), I.placed(d2, [])),
      List.append(&2, String, I.walk(I.tag(raw), fix, [], d), []),
      I.walk(I.tag(raw), fix, [], d),
      Equal.cong(List<&2, String>, List<&2, String>,
        y => List.append(&2, String, I.walk(I.tag(raw), fix, [], d), y),
        I.placed(d2, []), [], placed_nil(d2)),
      M2.lines_app_nil(I.walk(I.tag(raw), fix, [], d))))

# LAW: the second run over a block of rules and allowlist lines, whose own
# block is those allowlist lines: it gives the block back
law idem_block:
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +fix2: List<&2, String>
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, n, a1 <> as)), fix2, a1 <> as, False{})
    == List.append(&2, String, n, a1 <> as) : List<&2, String>}

def idem_block(n, a1, as, fix2, en, ea):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(List.append(&2, String, n, a1 <> as)), fix2, a1 <> as, False{}),
    List.append(&2, String, n, I.walk(I.tag(a1 <> as), fix2, a1 <> as, False{})),
    List.append(&2, String, n, a1 <> as),
    walk_kept(n, a1 <> as, fix2, a1 <> as, False{}, en),
    Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, n, y),
      I.walk(I.tag(a1 <> as), fix2, a1 <> as, False{}), a1 <> as,
      Equal.trans(List<&2, String>,
        I.walk(I.tag(a1 <> as), fix2, a1 <> as, False{}),
        I.walk(I.tag(List.append(&2, String, a1 <> as, [])), fix2, a1 <> as, False{}),
        a1 <> as,
        Equal.cong(List<&2, String>, List<&2, String>,
          y => I.walk(I.tag(y), fix2, a1 <> as, False{}),
          a1 <> as, List.append(&2, String, a1 <> as, []),
          Equal.sym(List<&2, String>, List.append(&2, String, a1 <> as, []), a1 <> as,
            M2.lines_app_nil(a1 <> as))),
        Equal.trans(List<&2, String>,
          I.walk(I.tag(List.append(&2, String, a1 <> as, [])), fix2, a1 <> as, False{}),
          List.append(&2, String, a1 <> as, I.walk(I.tag([]), fix2, a1 <> as, True{})),
          a1 <> as,
          first_allow(a1, as, [], fix2, a1 <> as, ea),
          M2.lines_app_nil(a1 <> as)))))

# LAW: the second run over the block the first put down in an allowlist
# line's place, and what the first wrote after it: the block comes back
# where it was, and the rest is kept
law idem_allow:
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +r: List<&2, String>
  for +fix2: List<&2, String>
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  for +er: {kept.all(r) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, List.append(&2, String, n, a1 <> as), r)),
    fix2, a1 <> as, False{})
    == List.append(&2, String, List.append(&2, String, n, a1 <> as), r) : List<&2, String>}

def idem_allow(n, a1, as, r, fix2, en, ea, er):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(List.append(&2, String, List.append(&2, String, n, a1 <> as), r)),
      fix2, a1 <> as, False{}),
    I.walk(I.tag(List.append(&2, String, n, List.append(&2, String, a1 <> as, r))),
      fix2, a1 <> as, False{}),
    List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
    Equal.cong(List<&2, String>, List<&2, String>,
      y => I.walk(I.tag(y), fix2, a1 <> as, False{}),
      List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
      List.append(&2, String, n, List.append(&2, String, a1 <> as, r)),
      lines_assoc(n, a1 <> as, r)),
    Equal.trans(List<&2, String>,
      I.walk(I.tag(List.append(&2, String, n, List.append(&2, String, a1 <> as, r))),
        fix2, a1 <> as, False{}),
      List.append(&2, String, n,
        I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{})),
      List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
      walk_kept(n, List.append(&2, String, a1 <> as, r), fix2, a1 <> as, False{}, en),
      Equal.trans(List<&2, String>,
        List.append(&2, String, n,
          I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{})),
        List.append(&2, String, n, List.append(&2, String, a1 <> as, r)),
        List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
        Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, n, y),
          I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{}),
          List.append(&2, String, a1 <> as, r),
          Equal.trans(List<&2, String>,
            I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{}),
            List.append(&2, String, a1 <> as, I.walk(I.tag(r), fix2, a1 <> as, True{})),
            List.append(&2, String, a1 <> as, r),
            first_allow(a1, as, r, fix2, a1 <> as, ea),
            Equal.cong(List<&2, String>, List<&2, String>,
              y => List.append(&2, String, a1 <> as, y),
              I.walk(I.tag(r), fix2, a1 <> as, True{}), r,
              Equal.trans(List<&2, String>,
                I.walk(I.tag(r), fix2, a1 <> as, True{}),
                List.append(&2, String, r, []),
                r,
                walk_clean(r, fix2, a1 <> as, True{}, er),
                M2.lines_app_nil(r))))),
        Equal.sym(List<&2, String>,
          List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
          List.append(&2, String, n, List.append(&2, String, a1 <> as, r)),
          lines_assoc(n, a1 <> as, r)))))

# LAW: one line of the first run, with its kind given as a parameter: the
# second run, whose block is the first run's allowlist lines, gives back
# what the first wrote for it and after it
law idem_walk.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +fix2: List<&2, String>
  for ek: {I.kind(h) == k : I.Rule}
  for +ef: {kept.all(fix) == True{} : Bool}
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  for ih: {I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
    fix2, a1 <> as, False{})
    == I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}) : List<&2, String>}
  {I.walk(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, List.append(&2, String, n, a1 <> as),
    False{})), fix2, a1 <> as, False{})
    == I.walk(I.Line{k, h} <> I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})
    : List<&2, String>}

def idem_walk.arm(k, h, t, fix, n, a1, as, fix2, ek, ef, en, ea, ih):
  match k:
    case I.Other{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Other{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Other{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Star{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Star{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Star{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Lib{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Lib{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Lib{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Pkgs{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Pkgs{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Pkgs{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Dir{}:
      Equal.trans(List<&2, String>,
        I.walk(I.tag(List.append(&2, String, fix,
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}))),
          fix2, a1 <> as, False{}),
        List.append(&2, String, fix, I.walk(I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{})),
        List.append(&2, String, fix,
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
        walk_kept(fix, I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
          fix2, a1 <> as, False{}, ef),
        Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, fix, y),
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Allow{x}:
      idem_allow(n, a1, as,
        I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), True{}), fix2, en, ea,
        walk_kept_out(t, fix, List.append(&2, String, n, a1 <> as), True{}, ef, {==}))

# LAW: the second run, whose block is the first run's allowlist lines, gives
# back what the first run wrote, when the first run's rules and the rules in
# front of its block are kept as they are
law idem_walk:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +fix2: List<&2, String>
  for +ef: {kept.all(fix) == True{} : Bool}
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  {I.walk(I.tag(I.walk(I.tag(raw), fix, List.append(&2, String, n, a1 <> as), False{})),
    fix2, a1 <> as, False{})
    == I.walk(I.tag(raw), fix, List.append(&2, String, n, a1 <> as), False{})
    : List<&2, String>}

def idem_walk(raw, fix, n, a1, as, fix2, ef, en, ea):
  match raw:
    case []:
      idem_block(n, a1, as, fix2, en, ea)
    case +h <> +t:
      idem_walk.arm(I.kind(h), h, t, fix, n, a1, as, fix2, {==}, ef, en, ea,
        idem_walk(t, fix, n, a1, as, fix2, ef, en, ea))

# What the first run's output holds: no `.ez/` line, and each of the three
# rules when it holds a hash. A rule the file had is kept where it was; one it
# lacked went in where its `.ez/` line was, or in front of the block.

# LAW: an `or` of a bit and False is the bit
law or_false_ledger:
  for a: Bool
  {Bool.or(a, False{}) == a : Bool}

def or_false_ledger(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: an `or` of a bit and True is True
law or_true_ledger:
  for a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def or_true_ledger(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: an `or` of two halves that answered False
law or_ff:
  for a: Bool
  for b: Bool
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  {Bool.or(a, b) == False{} : Bool}

def or_ff(a, b, ea, eb):
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

# LAW: a scan that stops at a hit answers True, and one that goes on answers
# what the rest does, whatever else is `or`ed onto the rest
law step_or:
  for b: Bool
  for x: Bool
  for y: Bool
  {I.has.step(b, _u => Bool.or(x, y)) == Bool.or(I.has.step(b, _u => x), y) : Bool}

def step_or(b, _x, _y):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a run of lines has a kind of line when either half has one
law has_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +r: I.Rule
  {I.has(I.tag(List.append(&2, String, xs, ys)), r)
    == Bool.or(I.has(I.tag(xs), r), I.has(I.tag(ys), r)) : Bool}

def has_app(xs, ys, r):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), r), _u => I.has(I.tag(List.append(&2, String, t, ys)), r)),
        I.has.step(I.same(I.kind(h), r), _u => Bool.or(I.has(I.tag(t), r), I.has(I.tag(ys), r))),
        Bool.or(I.has.step(I.same(I.kind(h), r), _u => I.has(I.tag(t), r)), I.has(I.tag(ys), r)),
        Equal.cong(Bool, Bool, y => I.has.step(I.same(I.kind(h), r), _u => y),
          I.has(I.tag(List.append(&2, String, t, ys)), r),
          Bool.or(I.has(I.tag(t), r), I.has(I.tag(ys), r)), has_app(t, ys, r)),
        step_or(I.same(I.kind(h), r), I.has(I.tag(t), r), I.has(I.tag(ys), r)))

# LAW: a run whose front has a kind of line has it
law has_left:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(xs), r) == True{} : Bool}
  {I.has(I.tag(List.append(&2, String, xs, ys)), r) == True{} : Bool}

def has_left(xs, ys, r, e):
  %Equal.sym(Bool, I.has(I.tag(List.append(&2, String, xs, ys)), r),
    Bool.or(I.has(I.tag(xs), r), I.has(I.tag(ys), r)), has_app(xs, ys, r))
    : {_ == True{} : Bool}
  %Equal.sym(Bool, I.has(I.tag(xs), r), True{}, e)
    : {Bool.or(_, I.has(I.tag(ys), r)) == True{} : Bool}
  {==}

# LAW: and one whose back has it
law has_right:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(ys), r) == True{} : Bool}
  {I.has(I.tag(List.append(&2, String, xs, ys)), r) == True{} : Bool}

def has_right(xs, ys, r, e):
  %Equal.sym(Bool, I.has(I.tag(List.append(&2, String, xs, ys)), r),
    Bool.or(I.has(I.tag(xs), r), I.has(I.tag(ys), r)), has_app(xs, ys, r))
    : {_ == True{} : Bool}
  %Equal.sym(Bool, I.has(I.tag(ys), r), True{}, e)
    : {Bool.or(I.has(I.tag(xs), r), _) == True{} : Bool}
  or_true_ledger(I.has(I.tag(xs), r))

# LAW: a line in front of a run that has a kind of line leaves it with one
law has_cons.arm:
  for b: Bool
  for +w: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(w), r) == True{} : Bool}
  {I.has.step(b, _u => I.has(I.tag(w), r)) == True{} : Bool}

def has_cons.arm(b, _w, _r, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

law has_cons:
  for +h: String
  for +w: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(w), r) == True{} : Bool}
  {I.has(I.tag(h <> w), r) == True{} : Bool}

def has_cons(h, w, r, e):
  has_cons.arm(I.same(I.kind(h), r), w, r, e)

# LAW: a line of the kind in front of any run is one
law has_here:
  for +h: String
  for +w: List<&2, String>
  for +r: I.Rule
  for e: {I.same(I.kind(h), r) == True{} : Bool}
  {I.has(I.tag(h <> w), r) == True{} : Bool}

def has_here(h, w, r, e):
  %Equal.sym(Bool, I.same(I.kind(h), r), True{}, e)
    : {I.has.step(_, _u => I.has(I.tag(w), r)) == True{} : Bool}
  {==}

# LAW: a line that is not of the kind leaves the question to the rest
law has_rest:
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for es: {I.same(I.kind(h), r) == False{} : Bool}
  for e: {I.has(I.tag(h <> t), r) == True{} : Bool}
  {I.has(I.tag(t), r) == True{} : Bool}

def has_rest(h, t, r, es, e):
  Equal.trans(Bool,
    I.has(I.tag(t), r),
    I.has.step(I.same(I.kind(h), r), _u => I.has(I.tag(t), r)),
    True{},
    Equal.cong(Bool, Bool, c => I.has.step(c, _u => I.has(I.tag(t), r)),
      False{}, I.same(I.kind(h), r), Equal.sym(Bool, I.same(I.kind(h), r), False{}, es)),
    e)

# LAW: `.ez/` is none of the kinds the walk keeps
law same_dir_kept:
  for r: I.Rule
  for kr: {M1.keeps(r) == True{} : Bool}
  {I.same(I.Dir{}, r) == False{} : Bool}

def same_dir_kept(r, kr):
  match r:
    case I.Other{}:
      {==}
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.same(I.Dir{}, I.Dir{}) == False{} : Bool}, kr)
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{x}:
      Eq.bit.absurd(&2, {I.same(I.Dir{}, I.Allow{x}) == False{} : Bool}, kr)

# LAW: and an allowlist line is no kind `same` is asked about
law same_allow:
  for +x: String
  for r: I.Rule
  {I.same(I.Allow{x}, r) == False{} : Bool}

def same_allow(_x, r):
  match r:
    case I.Other{}:
      {==}
    case I.Dir{}:
      {==}
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{y}:
      {==}

# LAW: one line, with how its kind compares given as a parameter: a line of
# the kind in front of what the walk wrote is one, and otherwise the rest had
# one, which the walk kept
law has_kept.cons.arm:
  for b: Bool
  for +h: String
  for +t: List<&2, String>
  for +w: List<&2, String>
  for +r: I.Rule
  for eb: {I.same(I.kind(h), r) == b : Bool}
  for e: {I.has.step(b, _u => I.has(I.tag(t), r)) == True{} : Bool}
  for ih: {I.has(I.tag(t), r) == True{} : Bool} -> {I.has(I.tag(w), r) == True{} : Bool}
  {I.has(I.tag(h <> w), r) == True{} : Bool}

def has_kept.cons.arm(b, h, _t, w, r, eb, e, ih):
  match b:
    case True{}:
      has_here(h, w, r, eb)
    case False{}:
      has_cons(h, w, r, ih(e))

# LAW: one line of the walk, with its kind given as a parameter: a kind the
# walk keeps is still there after it
law has_kept.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +kr: {M1.keeps(r) == True{} : Bool}
  for e: {I.has(I.tag(h <> t), r) == True{} : Bool}
  for ihd: {I.has(I.tag(t), r) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), r) == True{} : Bool}
  for iht: {I.has(I.tag(t), r) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)), r) == True{} : Bool}

def has_kept.arm(k, h, t, r, fix, blk, d, ek, kr, e, ihd, iht):
  match k:
    case I.Other{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Star{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Lib{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Pkgs{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Dir{}:
      has_right(fix, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, r,
          Equal.trans(Bool, I.same(I.kind(h), r), I.same(I.Dir{}, r), False{},
            Equal.cong(I.Rule, Bool, q => I.same(q, r), I.kind(h), I.Dir{}, ek),
            same_dir_kept(r, kr)), e)))
    case I.Allow{x}:
      has_right(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), r,
        iht(has_rest(h, t, r,
          Equal.trans(Bool, I.same(I.kind(h), r), I.same(I.Allow{x}, r), False{},
            Equal.cong(I.Rule, Bool, q => I.same(q, r), I.kind(h), I.Allow{x}, ek),
            same_allow(x, r)), e)))

# LAW: a kind the walk keeps, when the file has a line of it, is in what the
# walk writes
law has_kept:
  for raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +kr: {M1.keeps(r) == True{} : Bool}
  for e: {I.has(I.tag(raw), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, d)), r) == True{} : Bool}

def has_kept(raw, r, fix, blk, d, kr, e):
  match raw:
    case []:
      Eq.bit.absurd(&2, {I.has(I.tag(I.walk(I.tag([]), fix, blk, d)), r) == True{} : Bool}, e)
    case +h <> +t:
      has_kept.arm(I.kind(h), h, t, r, fix, blk, d, {==}, kr, e,
        x => has_kept(t, r, fix, blk, d, kr, x),
        x => has_kept(t, r, fix, blk, True{}, kr, x))

# LAW: one line of the walk, with its kind given as a parameter: when the
# file has a `.ez/` line, what the rules have, what the walk writes has
law has_dir.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for e: {I.has(I.tag(h <> t), I.Dir{}) == True{} : Bool}
  for +hf: {I.has(I.tag(fix), r) == True{} : Bool}
  for ihd: {I.has(I.tag(t), I.Dir{}) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), r) == True{} : Bool}
  for iht: {I.has(I.tag(t), I.Dir{}) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)), r) == True{} : Bool}

def has_dir.arm(k, h, t, r, fix, blk, d, ek, e, hf, ihd, iht):
  match k:
    case I.Dir{}:
      has_left(fix, I.walk(I.tag(t), fix, blk, d), r, hf)
    case I.Other{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Other{}, ek), e)))
    case I.Star{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Star{}, ek), e)))
    case I.Lib{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Lib{}, ek), e)))
    case I.Pkgs{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Pkgs{}, ek), e)))
    case I.Allow{x}:
      has_right(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), r,
        iht(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Allow{x}, ek), e)))

# LAW: a file with a `.ez/` line gets the rules in its place, so what they
# have, what the walk writes has
law has_dir:
  for raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for e: {I.has(I.tag(raw), I.Dir{}) == True{} : Bool}
  for +hf: {I.has(I.tag(fix), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, d)), r) == True{} : Bool}

def has_dir(raw, r, fix, blk, d, e, hf):
  match raw:
    case []:
      Eq.bit.absurd(&2, {I.has(I.tag(I.walk(I.tag([]), fix, blk, d)), r) == True{} : Bool}, e)
    case +h <> +t:
      has_dir.arm(I.kind(h), h, t, r, fix, blk, d, {==}, e, hf,
        x => has_dir(t, r, fix, blk, d, x, hf),
        x => has_dir(t, r, fix, blk, True{}, x, hf))

# LAW: one line of the walk before the block is down, with its kind given as
# a parameter: what the block has, what the walk writes has
law has_blk.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {I.has(I.tag(blk), r) == True{} : Bool}
  for ih: {I.has(I.tag(I.walk(I.tag(t), fix, blk, False{})), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, False{})), r) == True{} : Bool}

def has_blk.arm(k, h, t, r, fix, blk, e, ih):
  match k:
    case I.Other{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Star{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Lib{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Pkgs{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Dir{}:
      has_right(fix, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Allow{x}:
      has_left(blk, I.walk(I.tag(t), fix, blk, True{}), r, e)

# LAW: the walk puts the block down once, so what the block has, what the
# walk writes has
law has_blk:
  for raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {I.has(I.tag(blk), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, False{})), r) == True{} : Bool}

def has_blk(raw, r, fix, blk, e):
  match raw:
    case []:
      e
    case +h <> +t:
      has_blk.arm(I.kind(h), h, t, r, fix, blk, e, has_blk(t, r, fix, blk, e))

# LAW: a rule the walk keeps, which the file has or the rules put in, is in
# what the walk writes, with whether the file has it and whether it has a
# `.ez/` line given as parameters. A file with no `.ez/` line gets the rules
# in front of the block.
law has_rule.arm:
  for +raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +a: List<&2, String>
  for s: Bool
  for dd: Bool
  for es: {I.has(I.tag(raw), r) == s : Bool}
  for edd: {I.has(I.tag(raw), I.Dir{}) == dd : Bool}
  for +kr: {M1.keeps(r) == True{} : Bool}
  for pr: {Bool.or(s, I.has(I.tag(fix), r)) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, List.append(&2, String, I.need(dd, fix), a),
    False{})), r) == True{} : Bool}

def has_rule.arm(raw, r, fix, a, s, dd, es, edd, kr, pr):
  match s dd:
    case True{} _:
      has_kept(raw, r, fix, List.append(&2, String, I.need(dd, fix), a), False{}, kr, es)
    case False{} True{}:
      has_dir(raw, r, fix, List.append(&2, String, I.need(True{}, fix), a), False{}, edd, pr)
    case False{} False{}:
      has_blk(raw, r, fix, List.append(&2, String, fix, a),
        has_left(fix, a, r, pr))

law has_rule:
  for +raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +a: List<&2, String>
  for +kr: {M1.keeps(r) == True{} : Bool}
  for pr: {Bool.or(I.has(I.tag(raw), r), I.has(I.tag(fix), r)) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix,
    List.append(&2, String, I.need(I.has(I.tag(raw), I.Dir{}), fix), a), False{})), r)
    == True{} : Bool}

def has_rule(raw, r, fix, a, kr, pr):
  has_rule.arm(raw, r, fix, a, I.has(I.tag(raw), r), I.has(I.tag(raw), I.Dir{}),
    {==}, {==}, kr, pr)

# LAW: the file has `.ez/*`, or the rules put it in
law rules_star:
  for s: Bool
  for l: Bool
  for p: Bool
  {Bool.or(s, I.has(I.tag(I.rules.go(s, l, p)), I.Star{})) == True{} : Bool}

def rules_star(s, l, p):
  match s l p:
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

# LAW: and `!.ez/lib`
law rules_lib:
  for s: Bool
  for l: Bool
  for p: Bool
  {Bool.or(l, I.has(I.tag(I.rules.go(s, l, p)), I.Lib{})) == True{} : Bool}

def rules_lib(s, l, p):
  match s l p:
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

# LAW: and `.ez/lib/*`
law rules_pkgs:
  for s: Bool
  for l: Bool
  for p: Bool
  {Bool.or(p, I.has(I.tag(I.rules.go(s, l, p)), I.Pkgs{})) == True{} : Bool}

def rules_pkgs(s, l, p):
  match s l p:
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

# LAW: the rules are none of them missing when all three are there
law rules_none:
  for a: Bool
  for b: Bool
  for c: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  for ec: {c == True{} : Bool}
  {I.rules.go(a, b, c) == [] : List<&2, String>}

def rules_none(a, b, c, ea, eb, ec):
  %Equal.sym(Bool, a, True{}, ea) : {I.rules.go(_, b, c) == [] : List<&2, String>}
  %Equal.sym(Bool, b, True{}, eb) : {I.rules.go(True{}, _, c) == [] : List<&2, String>}
  %Equal.sym(Bool, c, True{}, ec) : {I.rules.go(True{}, True{}, _) == [] : List<&2, String>}
  {==}

# LAW: the three rules are kept as they are, whichever of them are written
law rules_kept:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {kept.all(I.rules.go(b1, b2, b3)) == True{} : Bool}

def rules_kept(b1, b2, b3):
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

# LAW: and none of them is `.ez/`
law rules_nodir:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {I.has(I.tag(I.rules.go(b1, b2, b3)), I.Dir{}) == False{} : Bool}

def rules_nodir(b1, b2, b3):
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

# LAW: the rules, written or not, are kept as they are
law need_kept:
  for s: Bool
  for +rs: List<&2, String>
  for h: {kept.all(rs) == True{} : Bool}
  {kept.all(I.need(s, rs)) == True{} : Bool}

def need_kept(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: and are not `.ez/`
law need_nodir:
  for s: Bool
  for +rs: List<&2, String>
  for h: {I.has(I.tag(rs), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.need(s, rs)), I.Dir{}) == False{} : Bool}

def need_nodir(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: the lines ez writes for hashes that name something are allowlist lines
law each_allowed:
  for +hs: List<&2, String>
  for +e: {M2.full.all(hs) == True{} : Bool}
  {allowed.all(I.allow.each(hs)) == True{} : Bool}

def each_allowed(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(I.Rule, I.kind(I.allow(h)), I.Allow{h}, M2.kind_allow(h, M2.full_head(h, t, e)))
        : {Bool.and(allowed(_), allowed.all(I.allow.each(t))) == True{} : Bool}
      each_allowed(t, M2.full_tail(h, t, e))

# LAW: and none of them is `.ez/`
law each_nodir:
  for +hs: List<&2, String>
  for +e: {M2.full.all(hs) == True{} : Bool}
  {I.has(I.tag(I.allow.each(hs)), I.Dir{}) == False{} : Bool}

def each_nodir(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(I.Rule, I.kind(I.allow(h)), I.Allow{h}, M2.kind_allow(h, M2.full_head(h, t, e)))
        : {I.has.step(I.same(_, I.Dir{}), _u => I.has(I.tag(I.allow.each(t)), I.Dir{}))
          == False{} : Bool}
      each_nodir(t, M2.full_tail(h, t, e))

# LAW: the block, put down or not, has no `.ez/` line when it has none
law placed_nodir:
  for +d: Bool
  for +blk: List<&2, String>
  for hb: {I.has(I.tag(blk), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.placed(d, blk)), I.Dir{}) == False{} : Bool}

def placed_nodir(d, _blk, hb):
  match d:
    case True{}:
      {==}
    case False{}:
      hb

# LAW: one line of the walk, with its kind given as a parameter: the walk
# writes no `.ez/` line when neither the rules nor the block has one
law has_nodir.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +hf: {I.has(I.tag(fix), I.Dir{}) == False{} : Bool}
  for +hb: {I.has(I.tag(blk), I.Dir{}) == False{} : Bool}
  for ihd: {I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{}) == False{} : Bool}
  for iht: {I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)), I.Dir{}) == False{} : Bool}

def has_nodir.arm(k, h, t, fix, blk, d, ek, hf, hb, ihd, iht):
  match k:
    case I.Other{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Other{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Other{}, ek),
        ihd)
    case I.Star{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Star{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Star{}, ek),
        ihd)
    case I.Lib{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Lib{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Lib{}, ek),
        ihd)
    case I.Pkgs{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Pkgs{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Pkgs{}, ek),
        ihd)
    case I.Dir{}:
      Equal.trans(Bool,
        I.has(I.tag(List.append(&2, String, fix, I.walk(I.tag(t), fix, blk, d))), I.Dir{}),
        Bool.or(I.has(I.tag(fix), I.Dir{}), I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        has_app(fix, I.walk(I.tag(t), fix, blk, d), I.Dir{}),
        or_ff(I.has(I.tag(fix), I.Dir{}), I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{}),
          hf, ihd))
    case I.Allow{x}:
      Equal.trans(Bool,
        I.has(I.tag(List.append(&2, String, I.placed(d, blk),
          I.walk(I.tag(t), fix, blk, True{}))), I.Dir{}),
        Bool.or(I.has(I.tag(I.placed(d, blk)), I.Dir{}),
          I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), I.Dir{})),
        False{},
        has_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), I.Dir{}),
        or_ff(I.has(I.tag(I.placed(d, blk)), I.Dir{}),
          I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), I.Dir{}),
          placed_nodir(d, blk, hb), iht))

# LAW: the walk writes no `.ez/` line when neither the rules nor the block
# has one: every `.ez/` line of the file is replaced
law has_nodir:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +hf: {I.has(I.tag(fix), I.Dir{}) == False{} : Bool}
  for +hb: {I.has(I.tag(blk), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, d)), I.Dir{}) == False{} : Bool}

def has_nodir(raw, fix, blk, d, hf, hb):
  match raw:
    case []:
      placed_nodir(d, blk, hb)
    case +h <> +t:
      has_nodir.arm(I.kind(h), h, t, fix, blk, d, {==}, hf, hb,
        has_nodir(t, fix, blk, d, hf, hb),
        has_nodir(t, fix, blk, True{}, hf, hb))

# LAW: the second run over a first run that put no block down, whose own
# block is empty too, gives the first run's output back
law idem_none:
  for +ls: List<&2, String>
  {M3.two(ls, [], True{}, []) == M3.one(ls, []) : List<&2, String>}

def idem_none(ls):
  Equal.trans(List<&2, String>,
    M3.two(ls, [], True{}, []),
    I.walk(I.tag(M3.one(ls, [])), I.rules(I.tag(M3.one(ls, []))), [], False{}),
    M3.one(ls, []),
    Equal.cong(Bool, List<&2, String>,
      x => I.walk(I.tag(M3.one(ls, [])), I.rules(I.tag(M3.one(ls, []))),
        List.append(&2, String, I.need(x, I.rules(I.tag(M3.one(ls, [])))), []), False{}),
      Bool.or(I.has(I.tag(M3.one(ls, [])), I.Dir{}), True{}), True{},
      or_true_ledger(I.has(I.tag(M3.one(ls, [])), I.Dir{}))),
    idem_nil(ls, I.rules(I.tag(ls)), I.rules(I.tag(M3.one(ls, []))), False{}, False{},
      rules_kept(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))))

# LAW: what the first run writes over a ledger that vends a hash has no
# `.ez/` line
law one_nodir:
  for +ls: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +e: {M2.full.all(a1 <> as) == True{} : Bool}
  {I.has(I.tag(M3.one(ls, List.append(&2, String,
    I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
    I.Dir{}) == False{} : Bool}

def one_nodir(ls, a1, as, e):
  has_nodir(ls, I.rules(I.tag(ls)),
    List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as)), False{},
    rules_nodir(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
      I.has(I.tag(ls), I.Pkgs{})),
    Equal.trans(Bool,
      I.has(I.tag(List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as))), I.Dir{}),
      Bool.or(I.has(I.tag(I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)))), I.Dir{}),
        I.has(I.tag(I.allow.each(a1 <> as)), I.Dir{})),
      False{},
      has_app(I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
        I.allow.each(a1 <> as), I.Dir{}),
      or_ff(I.has(I.tag(I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)))), I.Dir{}),
        I.has(I.tag(I.allow.each(a1 <> as)), I.Dir{}),
        need_nodir(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)),
          rules_nodir(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
            I.has(I.tag(ls), I.Pkgs{}))),
        each_nodir(a1 <> as, e))))

# LAW: and lacks none of the three rules
law one_rules:
  for +ls: List<&2, String>
  for +a: List<&2, String>
  {I.rules(I.tag(M3.one(ls, List.append(&2, String,
    I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a)))) == [] : List<&2, String>}

def one_rules(ls, a):
  rules_none(
    I.has(I.tag(M3.one(ls, List.append(&2, String,
      I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a))), I.Star{}),
    I.has(I.tag(M3.one(ls, List.append(&2, String,
      I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a))), I.Lib{}),
    I.has(I.tag(M3.one(ls, List.append(&2, String,
      I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a))), I.Pkgs{}),
    has_rule(ls, I.Star{}, I.rules(I.tag(ls)), a, {==},
      rules_star(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))),
    has_rule(ls, I.Lib{}, I.rules(I.tag(ls)), a, {==},
      rules_lib(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))),
    has_rule(ls, I.Pkgs{}, I.rules(I.tag(ls)), a, {==},
      rules_pkgs(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))))

# LAW: the second run over a first run that put a block of hashes down gives
# the first run's output back: its own block is those hashes' lines, which
# go back where they were
law idem_some:
  for +ls: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +e: {M2.full.all(a1 <> as) == True{} : Bool}
  {M3.two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
    I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as))
    == M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as))) : List<&2, String>}

def idem_some(ls, a1, as, e):
  Equal.trans(List<&2, String>,
    M3.two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
    I.walk(I.tag(M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
      I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
      I.rules(I.tag(M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
      I.allow.each(a1 <> as), False{}),
    M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as))),
    Equal.cong(List<&2, String>, List<&2, String>,
      y => I.walk(I.tag(M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
        I.rules(I.tag(M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as))))), y, False{}),
      List.append(&2, String,
        I.need(Bool.or(I.has(I.tag(M3.one(ls, List.append(&2, String,
          I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
          I.Dir{}), False{}),
          I.rules(I.tag(M3.one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))))),
        I.allow.each(a1 <> as)),
      I.allow.each(a1 <> as),
      Equal.trans(List<&2, String>,
        List.append(&2, String,
          I.need(Bool.or(I.has(I.tag(M3.one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
            I.Dir{}), False{}),
            I.rules(I.tag(M3.one(ls, List.append(&2, String,
              I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))))),
          I.allow.each(a1 <> as)),
        List.append(&2, String,
          I.rules(I.tag(M3.one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
          I.allow.each(a1 <> as)),
        I.allow.each(a1 <> as),
        Equal.cong(Bool, List<&2, String>,
          x => List.append(&2, String,
            I.need(Bool.or(x, False{}),
              I.rules(I.tag(M3.one(ls, List.append(&2, String,
                I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))))),
            I.allow.each(a1 <> as)),
          I.has(I.tag(M3.one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
            I.Dir{}),
          False{}, one_nodir(ls, a1, as, e)),
        Equal.cong(List<&2, String>, List<&2, String>,
          y => List.append(&2, String, y, I.allow.each(a1 <> as)),
          I.rules(I.tag(M3.one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
          [], one_rules(ls, I.allow.each(a1 <> as))))),
    idem_walk(ls, I.rules(I.tag(ls)), I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow(a1), I.allow.each(as),
      I.rules(I.tag(M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
      rules_kept(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{})),
      need_kept(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)),
        rules_kept(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
          I.has(I.tag(ls), I.Pkgs{}))),
      each_allowed(a1 <> as, e)))

# LAW: `I.lines` run again on the lines it made, with the vendored hashes
# given as a parameter that names something at every hash
law lines_idem.arm:
  for +ls: List<&2, String>
  for v: List<&2, String>
  for +e: {M2.full.all(v) == True{} : Bool}
  {M3.two(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}),
    List.is_empty(&2, String, v)), I.rules(I.tag(ls))), I.allow.each(v)),
    List.is_empty(&2, String, v), I.allow.each(v))
    == M3.one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}),
      List.is_empty(&2, String, v)), I.rules(I.tag(ls))), I.allow.each(v)))
    : List<&2, String>}

def lines_idem.arm(ls, v, e):
  match v:
    case []:
      Equal.trans(List<&2, String>,
        M3.two(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
          I.rules(I.tag(ls))), []), True{}, []),
        M3.two(ls, [], True{}, []),
        M3.one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
          I.rules(I.tag(ls))), [])),
        Equal.cong(Bool, List<&2, String>,
          x => M3.two(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))), []), True{}, []),
          Bool.or(I.has(I.tag(ls), I.Dir{}), True{}), True{},
          or_true_ledger(I.has(I.tag(ls), I.Dir{}))),
        Equal.trans(List<&2, String>,
          M3.two(ls, [], True{}, []),
          M3.one(ls, []),
          M3.one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
            I.rules(I.tag(ls))), [])),
          idem_none(ls),
          Equal.cong(Bool, List<&2, String>,
            x => M3.one(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))), [])),
            True{}, Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
            Equal.sym(Bool, Bool.or(I.has(I.tag(ls), I.Dir{}), True{}), True{},
              or_true_ledger(I.has(I.tag(ls), I.Dir{}))))))
    case +a1 <> +as:
      Equal.trans(List<&2, String>,
        M3.two(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
        M3.two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
        M3.one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as))),
        Equal.cong(Bool, List<&2, String>,
          x => M3.two(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))),
            I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
          Bool.or(I.has(I.tag(ls), I.Dir{}), False{}), I.has(I.tag(ls), I.Dir{}),
          or_false_ledger(I.has(I.tag(ls), I.Dir{}))),
        Equal.trans(List<&2, String>,
          M3.two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
            I.rules(I.tag(ls))), I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
          M3.one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
            I.rules(I.tag(ls))), I.allow.each(a1 <> as))),
          M3.one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
            I.rules(I.tag(ls))), I.allow.each(a1 <> as))),
          idem_some(ls, a1, as, e),
          Equal.cong(Bool, List<&2, String>,
            x => M3.one(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))),
              I.allow.each(a1 <> as))),
            I.has(I.tag(ls), I.Dir{}), Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
            Equal.sym(Bool, Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
              I.has(I.tag(ls), I.Dir{}), or_false_ledger(I.has(I.tag(ls), I.Dir{}))))))

# LAW: `I.lines` run on the lines it made gives them back
law lines_idem:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  {I.lines(ds, I.lines(ds, ls)) == I.lines(ds, ls) : List<&2, String>}

def lines_idem(ds, ls):
  lines_idem.arm(ls, I.vended(ds), M2.vended_full(ds))

# LAW: `sync` run on the file it wrote, with whether the first run changed
# the lines given as a parameter. An unchanged file was already in sync; a
# changed one reads back as the lines `I.lines` made, which it makes again.
law sync_idem.arm:
  for +ds: List<&2, M.Dep>
  for +text: String
  for b: Bool
  for eb: {String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
    I.file.text(I.file.lines(text))) == b : Bool}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.sync(ds, I.text.out(b, text, I.file.text(I.lines(ds, I.file.lines(text)))))
    == I.text.out(b, text, I.file.text(I.lines(ds, I.file.lines(text)))) : String}

def sync_idem.arm(ds, text, b, eb, ev):
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
        I.file.text(I.file.lines(text))), True{}, eb)
        : {I.text.out(_, text, I.file.text(I.lines(ds, I.file.lines(text)))) == text : String}
      {==}
    case False{}:
      %Equal.sym(List<&2, String>,
        I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
        I.lines(ds, I.file.lines(text)),
        M2.file_lines_text(I.lines(ds, I.file.lines(text)),
          M2.lines_clear(ds, I.file.lines(text), M2.file_lines_clear(text), ev)))
        : {I.text.out(String.eq(I.file.text(I.lines(ds, _)), I.file.text(_)),
          I.file.text(I.lines(ds, I.file.lines(text))), I.file.text(I.lines(ds, _)))
          == I.file.text(I.lines(ds, I.file.lines(text))) : String}
      %Equal.sym(List<&2, String>, I.lines(ds, I.lines(ds, I.file.lines(text))),
        I.lines(ds, I.file.lines(text)), lines_idem(ds, I.file.lines(text)))
        : {I.text.out(String.eq(I.file.text(_),
          I.file.text(I.lines(ds, I.file.lines(text)))),
          I.file.text(I.lines(ds, I.file.lines(text))), I.file.text(_))
          == I.file.text(I.lines(ds, I.file.lines(text))) : String}
      %Equal.sym(Bool, String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
        I.file.text(I.lines(ds, I.file.lines(text)))), True{},
        Eq.string_eq_self(I.file.text(I.lines(ds, I.file.lines(text)))))
        : {I.text.out(_, I.file.text(I.lines(ds, I.file.lines(text))),
          I.file.text(I.lines(ds, I.file.lines(text))))
          == I.file.text(I.lines(ds, I.file.lines(text))) : String}
      {==}

def L1.sync_idempotent(ds, text, ev):
  sync_idem.arm(ds, text,
    String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
      I.file.text(I.file.lines(text))), {==}, ev)
