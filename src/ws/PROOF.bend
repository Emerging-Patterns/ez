# ws: the proofs. `bend PROOF.bend` is the gate.
#
# The member set is decided segment by segment, so every law about a path
# goes by induction on its segments, comparing each with itself
# (`Eq.string_eq_self`), and every law about the set goes by induction on
# the ledgers git listed, splitting on whether the one in front is the
# directory asked about.
import Base
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ./workspace.bend as W
import ./LAWS.bend as Laws

# a cut at the last segment, by induction on the segments before it: the
# last is compared with itself, and each one before it is put back in front
def Laws.cut_last(ds, word):
  match ds:
    case []:
      Equal.cong(Bool, Maybe<&2, List<&2, String>>, bb => W.cut.last(bb),
        String.eq(word, word), True{}, Eq.string_eq_self(word))
    case +dh <> dt:
      match dt:
        case []:
          Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, List<&2, String>>,
            mm => W.cut.cons(dh, mm), W.cut([word], word), Some{[]},
            Equal.cong(Bool, Maybe<&2, List<&2, String>>, bb => W.cut.last(bb),
              String.eq(word, word), True{}, Eq.string_eq_self(word)))
        case +th <> +tt:
          Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, List<&2, String>>,
            mm => W.cut.cons(dh, mm),
            W.cut(List.append(&2, String, th <> tt, [word]), word), Some{th <> tt},
            Laws.cut_last(th <> tt, word))

# `<dir>/*` cuts at `*` to `<dir>`
def Laws.entry_under(ds):
  Equal.cong(Maybe<&2, List<&2, String>>, W.Entry,
    mm => W.entry.go(mm, List.append(&2, String, ds, ["*"])),
    W.cut(List.append(&2, String, ds, ["*"]), "*"), Some{ds}, Laws.cut_last(ds, "*"))

# anything else cuts to nothing, and is read as it is
def Laws.entry_plain(ss, ev):
  Equal.cong(Maybe<&2, List<&2, String>>, W.Entry, mm => W.entry.go(mm, ss),
    W.cut(ss, "*"), None{}, ev)

# each segment of the parent compared with itself, then one segment more
def Laws.under_child(ps, nn):
  match ps:
    case []:
      {==}
    case +ph <> +pt:
      Str.and_true(String.eq(ph, ph), W.under(pt, List.append(&2, String, pt, [nn])),
        Eq.string_eq_self(ph), Laws.under_child(pt, nn))

# and two segments more is not one
def Laws.under_deeper(ps, nn, mm, rest):
  match ps:
    case []:
      {==}
    case +ph <> +pt:
      Equal.trans(Bool,
        Bool.and(String.eq(ph, ph), W.under(pt, List.append(&2, String, pt, nn <> mm <> rest))),
        Bool.and(String.eq(ph, ph), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(String.eq(ph, ph), bb),
          W.under(pt, List.append(&2, String, pt, nn <> mm <> rest)), False{},
          Laws.under_deeper(pt, nn, mm, rest)),
        Str.and_false(String.eq(ph, ph)))

# a directory under another agrees with it segment by segment as far as the
# other goes
def Laws.under_prefix(ps, ds, ev):
  match ps:
    case []:
      {==}
    case +ph <> +pt:
      match ds:
        case []:
          Eq.bit.absurd(&2, {Laws.prefix(ph <> pt, []) == True{} : Bool}, ev)
        case +dh <> +dt:
          Str.and_true(String.eq(ph, dh), Laws.prefix(pt, dt),
            Eq.and.left(String.eq(ph, dh), W.under(pt, dt), ev),
            Laws.under_prefix(pt, dt, Eq.and.right(String.eq(ph, dh), W.under(pt, dt), ev)))

# the bad segment makes its own `and` False, and every segment before it
# keeps it False
def Laws.segs_bad(ps, bad, qs, ev):
  match ps:
    case []:
      Equal.cong(Bool, Bool, bb => Bool.and(bb, W.segs.ok(qs)), W.seg.ok(bad), False{}, ev)
    case +ph <> +pt:
      Equal.trans(Bool,
        Bool.and(W.seg.ok(ph), W.segs.ok(List.append(&2, String, pt, bad <> qs))),
        Bool.and(W.seg.ok(ph), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(W.seg.ok(ph), bb),
          W.segs.ok(List.append(&2, String, pt, bad <> qs)), False{},
          Laws.segs_bad(pt, bad, qs, ev)),
        Str.and_false(W.seg.ok(ph)))

def Laws.seg_empty_refused(ps, qs):
  Laws.segs_bad(ps, "", qs, {==})

def Laws.seg_dot_refused(ps, qs):
  Laws.segs_bad(ps, ".", qs, {==})

def Laws.seg_up_refused(ps, qs):
  Laws.segs_bad(ps, "..", qs, {==})

def Laws.seg_star_refused(ps, qs):
  Laws.segs_bad(ps, "*", qs, {==})

# an `or` whose right half is True is True
def or_true(aa: Bool) -> {Bool.or(aa, True{}) == True{} : Bool}:
  match aa:
    case False{}:
      {==}
    case True{}:
      {==}

# the entry that names the directory makes its own `or` True, and every entry
# before it keeps it True
def Laws.listed_anywhere(fs, ee, es, ds, ev):
  match fs:
    case []:
      Equal.cong(Bool, Bool, bb => Bool.or(bb, W.listed(es, ds)), W.hit(ee, ds), True{}, ev)
    case +fh <> +ft:
      Equal.trans(Bool,
        Bool.or(W.hit(fh, ds), W.listed(List.append(&2, W.Entry, ft, ee <> es), ds)),
        Bool.or(W.hit(fh, ds), True{}),
        True{},
        Equal.cong(Bool, Bool, bb => Bool.or(W.hit(fh, ds), bb),
          W.listed(List.append(&2, W.Entry, ft, ee <> es), ds), True{},
          Laws.listed_anywhere(ft, ee, es, ds, ev)),
        or_true(W.hit(fh, ds)))

# an excluded directory's `not` is False, so its `and` is
def Laws.excluded_not_chosen(es, ex, ds, ev):
  Equal.trans(Bool,
    Bool.and(W.listed(es, ds), Bool.not(W.has(ex, ds))),
    Bool.and(W.listed(es, ds), False{}),
    False{},
    Equal.cong(Bool, Bool, bb => Bool.and(W.listed(es, ds), Bool.not(bb)), W.has(ex, ds), True{}, ev),
    Str.and_false(W.listed(es, ds)))

# two paths that compare equal segment by segment are one path
def segs_eq_true(
  as: List<&2, String>,
  bs: List<&2, String>,
  +ev: {W.segs.eq(as, bs) == True{} : Bool}
) -> {as == bs : List<&2, String>}:
  match as:
    case []:
      match bs:
        case []:
          {==}
        case bh <> bt:
          Eq.bit.absurd(&2, {[] == bh <> bt : List<&2, String>}, ev)
    case +ah <> +at:
      match bs:
        case []:
          Eq.bit.absurd(&2, {ah <> at == [] : List<&2, String>}, ev)
        case +bh <> +bt:
          Equal.trans(List<&2, String>, ah <> at, bh <> at, bh <> bt,
            Equal.cong(String, List<&2, String>, hh => hh <> at, ah, bh,
              Str.string_eq_true(ah, bh, Eq.and.left(String.eq(ah, bh), W.segs.eq(at, bt), ev))),
            Equal.cong(List<&2, String>, List<&2, String>, tt => bh <> tt, at, bt,
              segs_eq_true(at, bt, Eq.and.right(String.eq(ah, bh), W.segs.eq(at, bt), ev))))

# a ledger put in front of the rest, or not, is found where it was put
def put_has(
  kk: Bool,
  +ll: W.Ledger,
  +rr: List<&2, W.Ledger>,
  +ds: List<&2, String>
) -> {W.has(W.dirs.of(W.picks.put(kk, ll, rr)), ds)
    == Bool.or(Bool.and(kk, W.segs.eq(W.ledger.dir(ll), ds)), W.has(W.dirs.of(rr), ds)) : Bool}:
  match kk:
    case True{}:
      {==}
    case False{}:
      {==}

# the directory in front is the one asked about, so it is chosen exactly
# when that one is
def same_c(cc: Bool, hh: Bool) -> {Bool.or(Bool.and(cc, True{}), Bool.and(hh, cc)) == cc : Bool}:
  match cc:
    case True{}:
      {==}
    case False{}:
      Str.and_false(hh)

# it is not, so whether it is chosen does not matter
def other_c(
  kk: Bool,
  hh: Bool,
  cc: Bool
) -> {Bool.or(Bool.and(kk, False{}), Bool.and(hh, cc)) == Bool.and(hh, cc) : Bool}:
  match kk:
    case True{}:
      {==}
    case False{}:
      {==}

# one ledger's step, split on whether its directory is the one asked about
def picks.arm(
  ee: Bool,
  +spec: W.Spec,
  +ll: W.Ledger,
  +hh: Bool,
  +ds: List<&2, String>,
  +eq: {W.segs.eq(W.ledger.dir(ll), ds) == ee : Bool}
) -> {Bool.or(Bool.and(W.chosen(spec, W.ledger.dir(ll)), ee), Bool.and(hh, W.chosen(spec, ds)))
    == Bool.and(Bool.or(ee, hh), W.chosen(spec, ds)) : Bool}:
  match ee:
    case True{}:
      Equal.trans(Bool,
        Bool.or(Bool.and(W.chosen(spec, W.ledger.dir(ll)), True{}), Bool.and(hh, W.chosen(spec, ds))),
        Bool.or(Bool.and(W.chosen(spec, ds), True{}), Bool.and(hh, W.chosen(spec, ds))),
        W.chosen(spec, ds),
        Equal.cong(List<&2, String>, Bool,
          xs => Bool.or(Bool.and(W.chosen(spec, xs), True{}), Bool.and(hh, W.chosen(spec, ds))),
          W.ledger.dir(ll), ds, segs_eq_true(W.ledger.dir(ll), ds, eq)),
        same_c(W.chosen(spec, ds), hh))
    case False{}:
      other_c(W.chosen(spec, W.ledger.dir(ll)), hh, W.chosen(spec, ds))

# by induction on the ledgers: the one in front is put, or not, and found, or
# not, and the rest are the induction's
def Laws.picks_exactly(spec, ls, ds):
  match ls:
    case []:
      {==}
    case +lh <> +lt:
      Equal.trans(Bool,
        W.has(W.dirs.of(W.picks.put(W.chosen(spec, W.ledger.dir(lh)), lh, W.picks(spec, lt))), ds),
        Bool.or(Bool.and(W.chosen(spec, W.ledger.dir(lh)), W.segs.eq(W.ledger.dir(lh), ds)),
          W.has(W.dirs.of(W.picks(spec, lt)), ds)),
        Bool.and(Bool.or(W.segs.eq(W.ledger.dir(lh), ds), W.has(W.dirs.of(lt), ds)), W.chosen(spec, ds)),
        put_has(W.chosen(spec, W.ledger.dir(lh)), lh, W.picks(spec, lt), ds),
        Equal.trans(Bool,
          Bool.or(Bool.and(W.chosen(spec, W.ledger.dir(lh)), W.segs.eq(W.ledger.dir(lh), ds)),
            W.has(W.dirs.of(W.picks(spec, lt)), ds)),
          Bool.or(Bool.and(W.chosen(spec, W.ledger.dir(lh)), W.segs.eq(W.ledger.dir(lh), ds)),
            Bool.and(W.has(W.dirs.of(lt), ds), W.chosen(spec, ds))),
          Bool.and(Bool.or(W.segs.eq(W.ledger.dir(lh), ds), W.has(W.dirs.of(lt), ds)), W.chosen(spec, ds)),
          Equal.cong(Bool, Bool,
            bb => Bool.or(Bool.and(W.chosen(spec, W.ledger.dir(lh)), W.segs.eq(W.ledger.dir(lh), ds)), bb),
            W.has(W.dirs.of(W.picks(spec, lt)), ds),
            Bool.and(W.has(W.dirs.of(lt), ds), W.chosen(spec, ds)),
            Laws.picks_exactly(spec, lt, ds)),
          picks.arm(W.segs.eq(W.ledger.dir(lh), ds), spec, lh, W.has(W.dirs.of(lt), ds), ds, {==})))

# the missing entry makes its own `and` False, and every entry before it
# keeps it False
def Laws.present_anywhere(fs, ps, es, found, ev):
  match fs:
    case []:
      Equal.cong(Bool, Bool, bb => Bool.and(bb, W.present(es, found)), W.has(found, ps), False{}, ev)
    case +fh <> +ft:
      Equal.trans(Bool,
        Bool.and(W.present.one(fh, found), W.present(List.append(&2, W.Entry, ft, W.Plain{ps} <> es), found)),
        Bool.and(W.present.one(fh, found), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(W.present.one(fh, found), bb),
          W.present(List.append(&2, W.Entry, ft, W.Plain{ps} <> es), found), False{},
          Laws.present_anywhere(ft, ps, es, found, ev)),
        Str.and_false(W.present.one(fh, found)))

def Laws.members_when_ok(spec, root, ls, ev):
  Equal.cong(Bool, W.Members, bb => W.members.go(bb, spec, root, ls), W.ok(spec, root, ls), True{}, ev)

def Laws.members_refused(spec, root, ls, ev):
  Equal.cong(Bool, W.Members, bb => W.members.go(bb, spec, root, ls), W.ok(spec, root, ls), False{}, ev)

# the first of the four halves
def Laws.ok_needs_entries(es, ex, root, ls, ev):
  Eq.and.left(W.entries.ok(es),
    Bool.and(W.present(es, W.dirs.of(ls)),
      Bool.and(W.unnested(W.picks(W.Spec{es, ex}, ls)),
        W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls))))), ev)

# what is left once the first half is taken off
def ok.rest(
  +es: List<&2, W.Entry>,
  +ex: List<&2, List<&2, String>>,
  +root: W.Root,
  +ls: List<&2, W.Ledger>,
  +ev: {W.ok(W.Spec{es, ex}, root, ls) == True{} : Bool}
) -> {Bool.and(W.present(es, W.dirs.of(ls)),
    Bool.and(W.unnested(W.picks(W.Spec{es, ex}, ls)),
      W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls))))) == True{} : Bool}:
  Eq.and.right(W.entries.ok(es),
    Bool.and(W.present(es, W.dirs.of(ls)),
      Bool.and(W.unnested(W.picks(W.Spec{es, ex}, ls)),
        W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls))))), ev)

# and the last two, once the second is taken off
def ok.last(
  +es: List<&2, W.Entry>,
  +ex: List<&2, List<&2, String>>,
  +root: W.Root,
  +ls: List<&2, W.Ledger>,
  +ev: {W.ok(W.Spec{es, ex}, root, ls) == True{} : Bool}
) -> {Bool.and(W.unnested(W.picks(W.Spec{es, ex}, ls)),
    W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls)))) == True{} : Bool}:
  Eq.and.right(W.present(es, W.dirs.of(ls)),
    Bool.and(W.unnested(W.picks(W.Spec{es, ex}, ls)),
      W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls)))), ok.rest(es, ex, root, ls, ev))

def Laws.ok_needs_present(es, ex, root, ls, ev):
  Eq.and.left(W.present(es, W.dirs.of(ls)),
    Bool.and(W.unnested(W.picks(W.Spec{es, ex}, ls)),
      W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls)))), ok.rest(es, ex, root, ls, ev))

def Laws.ok_needs_unnested(spec, root, ls, ev):
  match spec:
    case W.Spec{+es, +ex}:
      Eq.and.left(W.unnested(W.picks(W.Spec{es, ex}, ls)),
        W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls))), ok.last(es, ex, root, ls, ev))

def Laws.ok_needs_names(spec, root, ls, ev):
  match spec:
    case W.Spec{+es, +ex}:
      Eq.and.right(W.unnested(W.picks(W.Spec{es, ex}, ls)),
        W.distinct(W.names(root, W.picks(W.Spec{es, ex}, ls))), ok.last(es, ex, root, ls, ev))
