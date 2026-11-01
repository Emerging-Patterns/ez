# proofs of laws/WorkspaceMembersChosen.bend
#
# The member set is decided segment by segment, so every law about a path
# goes by induction on its segments, comparing each with itself
# (`Eq.string_eq_self`), and every law about the set goes by induction on
# the ledgers git listed, splitting on whether the one in front is the
# directory asked about.
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/ws/workspace.bend as WWorkspace
import 0xc5d9d3e28b79ea98be22eb42c7e37802/main.bend as E
import ../laws/WorkspaceMembersChosen.bend as Laws
import ../laws/defs/PathPrefix.bend as D1

# a cut at the last segment, by induction on the segments before it: the
# last is compared with itself, and each one before it is put back in front
def Laws.cut_last(ds, word):
  match ds:
    case []:
      Equal.cong(Bool, Maybe<&2, List<&2, String>>, bb => WWorkspace.cut.last(bb),
        String.eq(word, word), True{}, Eq.string_eq_self(word))
    case +dh <> dt:
      match dt:
        case []:
          Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, List<&2, String>>,
            mm => WWorkspace.cut.cons(dh, mm), WWorkspace.cut([word], word), Some{[]},
            Equal.cong(Bool, Maybe<&2, List<&2, String>>, bb => WWorkspace.cut.last(bb),
              String.eq(word, word), True{}, Eq.string_eq_self(word)))
        case +th <> +tt:
          Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, List<&2, String>>,
            mm => WWorkspace.cut.cons(dh, mm),
            WWorkspace.cut(List.append(&2, String, th <> tt, [word]), word), Some{th <> tt},
            Laws.cut_last(th <> tt, word))

# `<dir>/*` cuts at `*` to `<dir>`
def Laws.entry_under(ds):
  Equal.cong(Maybe<&2, List<&2, String>>, WWorkspace.Entry,
    mm => WWorkspace.entry.go(mm, List.append(&2, String, ds, ["*"])),
    WWorkspace.cut(List.append(&2, String, ds, ["*"]), "*"), Some{ds}, Laws.cut_last(ds, "*"))

# anything else cuts to nothing, and is read as it is
def Laws.entry_plain(ss, ev):
  Equal.cong(Maybe<&2, List<&2, String>>, WWorkspace.Entry, mm => WWorkspace.entry.go(mm, ss),
    WWorkspace.cut(ss, "*"), None{}, ev)

# each segment of the parent compared with itself, then one segment more
def Laws.under_child(ps, nn):
  match ps:
    case []:
      {==}
    case +ph <> +pt:
      Str.and_true(String.eq(ph, ph), WWorkspace.under(pt, List.append(&2, String, pt, [nn])),
        Eq.string_eq_self(ph), Laws.under_child(pt, nn))

# and two segments more is not one
def Laws.under_deeper(ps, nn, mm, rest):
  match ps:
    case []:
      {==}
    case +ph <> +pt:
      Equal.trans(Bool,
        Bool.and(String.eq(ph, ph), WWorkspace.under(pt, List.append(&2, String, pt, nn <> mm <> rest))),
        Bool.and(String.eq(ph, ph), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(String.eq(ph, ph), bb),
          WWorkspace.under(pt, List.append(&2, String, pt, nn <> mm <> rest)), False{},
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
          Eq.bit.absurd(&2, {D1.prefix(ph <> pt, []) == True{} : Bool}, ev)
        case +dh <> +dt:
          Str.and_true(String.eq(ph, dh), D1.prefix(pt, dt),
            Eq.and.left(String.eq(ph, dh), WWorkspace.under(pt, dt), ev),
            Laws.under_prefix(pt, dt, Eq.and.right(String.eq(ph, dh), WWorkspace.under(pt, dt), ev)))

# the bad segment makes its own `and` False, and every segment before it
# keeps it False
def Laws.segs_bad(ps, bad, qs, ev):
  match ps:
    case []:
      Equal.cong(Bool, Bool, bb => Bool.and(bb, WWorkspace.segs.ok(qs)), WWorkspace.seg.ok(bad), False{}, ev)
    case +ph <> +pt:
      Equal.trans(Bool,
        Bool.and(WWorkspace.seg.ok(ph), WWorkspace.segs.ok(List.append(&2, String, pt, bad <> qs))),
        Bool.and(WWorkspace.seg.ok(ph), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(WWorkspace.seg.ok(ph), bb),
          WWorkspace.segs.ok(List.append(&2, String, pt, bad <> qs)), False{},
          Laws.segs_bad(pt, bad, qs, ev)),
        Str.and_false(WWorkspace.seg.ok(ph)))

def Laws.seg_empty_refused(ps, qs):
  Laws.segs_bad(ps, "", qs, {==})

def Laws.seg_dot_refused(ps, qs):
  Laws.segs_bad(ps, ".", qs, {==})

def Laws.seg_up_refused(ps, qs):
  Laws.segs_bad(ps, "..", qs, {==})

def Laws.seg_star_refused(ps, qs):
  Laws.segs_bad(ps, "*", qs, {==})

# an `or` whose right half is True is True
def or_true_ws(aa: Bool) -> {Bool.or(aa, True{}) == True{} : Bool}:
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
      Equal.cong(Bool, Bool, bb => Bool.or(bb, WWorkspace.listed(es, ds)), WWorkspace.hit(ee, ds), True{}, ev)
    case +fh <> +ft:
      Equal.trans(Bool,
        Bool.or(WWorkspace.hit(fh, ds), WWorkspace.listed(List.append(&2, WWorkspace.Entry, ft, ee <> es), ds)),
        Bool.or(WWorkspace.hit(fh, ds), True{}),
        True{},
        Equal.cong(Bool, Bool, bb => Bool.or(WWorkspace.hit(fh, ds), bb),
          WWorkspace.listed(List.append(&2, WWorkspace.Entry, ft, ee <> es), ds), True{},
          Laws.listed_anywhere(ft, ee, es, ds, ev)),
        or_true_ws(WWorkspace.hit(fh, ds)))

# an excluded directory's `not` is False, so its `and` is
def Laws.excluded_not_chosen(es, ex, ds, ev):
  Equal.trans(Bool,
    Bool.and(WWorkspace.listed(es, ds), Bool.not(WWorkspace.has(ex, ds))),
    Bool.and(WWorkspace.listed(es, ds), False{}),
    False{},
    Equal.cong(Bool, Bool, bb => Bool.and(WWorkspace.listed(es, ds), Bool.not(bb)), WWorkspace.has(ex, ds), True{}, ev),
    Str.and_false(WWorkspace.listed(es, ds)))

# two paths that compare equal segment by segment are one path
def segs_eq_true(
  as: List<&2, String>,
  bs: List<&2, String>,
  +ev: {WWorkspace.segs.eq(as, bs) == True{} : Bool}
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
              Str.string_eq_true(ah, bh, Eq.and.left(String.eq(ah, bh), WWorkspace.segs.eq(at, bt), ev))),
            Equal.cong(List<&2, String>, List<&2, String>, tt => bh <> tt, at, bt,
              segs_eq_true(at, bt, Eq.and.right(String.eq(ah, bh), WWorkspace.segs.eq(at, bt), ev))))

# a ledger put in front of the rest, or not, is found where it was put
def put_has(
  kk: Bool,
  +ll: WWorkspace.Ledger,
  +rr: List<&2, WWorkspace.Ledger>,
  +ds: List<&2, String>
) -> {WWorkspace.has(WWorkspace.dirs.of(WWorkspace.picks.put(kk, ll, rr)), ds)
    == Bool.or(Bool.and(kk, WWorkspace.segs.eq(WWorkspace.ledger.dir(ll), ds)), WWorkspace.has(WWorkspace.dirs.of(rr), ds)) : Bool}:  # noqa: S002
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
  +spec: WWorkspace.Spec,
  +ll: WWorkspace.Ledger,
  +hh: Bool,
  +ds: List<&2, String>,
  +eq: {WWorkspace.segs.eq(WWorkspace.ledger.dir(ll), ds) == ee : Bool}
) -> {Bool.or(Bool.and(WWorkspace.chosen(spec, WWorkspace.ledger.dir(ll)), ee), Bool.and(hh, WWorkspace.chosen(spec,
    ds)))
    == Bool.and(Bool.or(ee, hh), WWorkspace.chosen(spec, ds)) : Bool}:
  match ee:
    case True{}:
      Equal.trans(Bool,
        Bool.or(Bool.and(WWorkspace.chosen(spec, WWorkspace.ledger.dir(ll)), True{}), Bool.and(hh,
            WWorkspace.chosen(spec, ds))),
        Bool.or(Bool.and(WWorkspace.chosen(spec, ds), True{}), Bool.and(hh, WWorkspace.chosen(spec, ds))),
        WWorkspace.chosen(spec, ds),
        Equal.cong(List<&2, String>, Bool,
          xs => Bool.or(Bool.and(WWorkspace.chosen(spec, xs), True{}), Bool.and(hh, WWorkspace.chosen(spec, ds))),
          WWorkspace.ledger.dir(ll), ds, segs_eq_true(WWorkspace.ledger.dir(ll), ds, eq)),
        same_c(WWorkspace.chosen(spec, ds), hh))
    case False{}:
      other_c(WWorkspace.chosen(spec, WWorkspace.ledger.dir(ll)), hh, WWorkspace.chosen(spec, ds))

# by induction on the ledgers: the one in front is put, or not, and found, or
# not, and the rest are the induction's
def Laws.picks_exactly(spec, ls, ds):
  match ls:
    case []:
      {==}
    case +lh <> +lt:
      Equal.trans(Bool,
        WWorkspace.has(WWorkspace.dirs.of(WWorkspace.picks.put(WWorkspace.chosen(spec, WWorkspace.ledger.dir(lh)), lh,
            WWorkspace.picks(spec, lt))), ds),
        Bool.or(Bool.and(WWorkspace.chosen(spec, WWorkspace.ledger.dir(lh)),
            WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds)),
          WWorkspace.has(WWorkspace.dirs.of(WWorkspace.picks(spec, lt)), ds)),
        Bool.and(Bool.or(WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds), WWorkspace.has(WWorkspace.dirs.of(lt),
            ds)), WWorkspace.chosen(spec, ds)),
        put_has(WWorkspace.chosen(spec, WWorkspace.ledger.dir(lh)), lh, WWorkspace.picks(spec, lt), ds),
        Equal.trans(Bool,
          Bool.or(Bool.and(WWorkspace.chosen(spec, WWorkspace.ledger.dir(lh)),
              WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds)),
            WWorkspace.has(WWorkspace.dirs.of(WWorkspace.picks(spec, lt)), ds)),
          Bool.or(Bool.and(WWorkspace.chosen(spec, WWorkspace.ledger.dir(lh)),
              WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds)),
            Bool.and(WWorkspace.has(WWorkspace.dirs.of(lt), ds), WWorkspace.chosen(spec, ds))),
          Bool.and(Bool.or(WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds), WWorkspace.has(WWorkspace.dirs.of(lt),
              ds)), WWorkspace.chosen(spec, ds)),
          Equal.cong(Bool, Bool,
            bb => Bool.or(Bool.and(WWorkspace.chosen(spec, WWorkspace.ledger.dir(lh)),
                WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds)), bb),
            WWorkspace.has(WWorkspace.dirs.of(WWorkspace.picks(spec, lt)), ds),
            Bool.and(WWorkspace.has(WWorkspace.dirs.of(lt), ds), WWorkspace.chosen(spec, ds)),
            Laws.picks_exactly(spec, lt, ds)),
          picks.arm(WWorkspace.segs.eq(WWorkspace.ledger.dir(lh), ds), spec, lh, WWorkspace.has(WWorkspace.dirs.of(lt),
              ds), ds, {==})))

# the missing entry makes its own `and` False, and every entry before it
# keeps it False
def Laws.present_anywhere(fs, ps, es, found, ev):
  match fs:
    case []:
      Equal.cong(Bool, Bool, bb => Bool.and(bb, WWorkspace.present(es, found)), WWorkspace.has(found, ps), False{}, ev)
    case +fh <> +ft:
      Equal.trans(Bool,
        Bool.and(WWorkspace.present.one(fh, found), WWorkspace.present(List.append(&2, WWorkspace.Entry, ft,
            WWorkspace.Plain{ps} <> es), found)),
        Bool.and(WWorkspace.present.one(fh, found), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(WWorkspace.present.one(fh, found), bb),
          WWorkspace.present(List.append(&2, WWorkspace.Entry, ft, WWorkspace.Plain{ps} <> es), found), False{},
          Laws.present_anywhere(ft, ps, es, found, ev)),
        Str.and_false(WWorkspace.present.one(fh, found)))

def Laws.members_when_ok(spec, root, ls, ev):
  Equal.cong(Bool, WWorkspace.Members, bb => WWorkspace.members.go(bb, spec, root, ls), WWorkspace.ok(spec, root, ls),
      True{}, ev)

def Laws.members_refused(spec, root, ls, ev):
  Equal.cong(Bool, WWorkspace.Members, bb => WWorkspace.members.go(bb, spec, root, ls), WWorkspace.ok(spec, root, ls),
      False{}, ev)

# the first of the four halves
def Laws.ok_needs_entries(es, ex, root, ls, ev):
  Eq.and.left(WWorkspace.entries.ok(es),
    Bool.and(WWorkspace.present(es, WWorkspace.dirs.of(ls)),
      Bool.and(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
        WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls))))), ev)

# what is left once the first half is taken off
def ok.rest(
  +es: List<&2, WWorkspace.Entry>,
  +ex: List<&2, List<&2, String>>,
  +root: WWorkspace.Root,
  +ls: List<&2, WWorkspace.Ledger>,
  +ev: {WWorkspace.ok(WWorkspace.Spec{es, ex}, root, ls) == True{} : Bool}
) -> {Bool.and(WWorkspace.present(es, WWorkspace.dirs.of(ls)),
    Bool.and(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
      WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls))))) == True{} : Bool}:
  Eq.and.right(WWorkspace.entries.ok(es),
    Bool.and(WWorkspace.present(es, WWorkspace.dirs.of(ls)),
      Bool.and(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
        WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls))))), ev)

# and the last two, once the second is taken off
def ok.last(
  +es: List<&2, WWorkspace.Entry>,
  +ex: List<&2, List<&2, String>>,
  +root: WWorkspace.Root,
  +ls: List<&2, WWorkspace.Ledger>,
  +ev: {WWorkspace.ok(WWorkspace.Spec{es, ex}, root, ls) == True{} : Bool}
) -> {Bool.and(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
    WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)))) == True{} : Bool}:
  Eq.and.right(WWorkspace.present(es, WWorkspace.dirs.of(ls)),
    Bool.and(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
      WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)))), ok.rest(es, ex,
          root, ls, ev))

def Laws.ok_needs_present(es, ex, root, ls, ev):
  Eq.and.left(WWorkspace.present(es, WWorkspace.dirs.of(ls)),
    Bool.and(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
      WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)))), ok.rest(es, ex,
          root, ls, ev))

def Laws.ok_needs_unnested(spec, root, ls, ev):
  match spec:
    case WWorkspace.Spec{+es, +ex}:
      Eq.and.left(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
        WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls))), ok.last(es, ex,
            root, ls, ev))

def Laws.ok_needs_names(spec, root, ls, ev):
  match spec:
    case WWorkspace.Spec{+es, +ex}:
      Eq.and.right(WWorkspace.unnested(WWorkspace.picks(WWorkspace.Spec{es, ex}, ls)),
        WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(WWorkspace.Spec{es, ex}, ls))), ok.last(es, ex,
            root, ls, ev))

# ---------------------------------------------------------------------------
# reading the `[workspace]` table

def Laws.spec_finds_table(_path, _sub, _rest):
  {==}

def Laws.spec_none_lone(_path, sub, ch, tt, rest, ev):
  Equal.cong(Bool, WWorkspace.Read, bb => WWorkspace.spec.at(bb, sub, WWorkspace.spec.rows(rest)),
    String.eq(SCon{ch, tt}, "workspace"), False{}, ev)

def Laws.table_reads(rows, ms, xs, em, ex):
  Equal.trans(WWorkspace.Read,
    WWorkspace.table.go(WWorkspace.array(rows, "members"), WWorkspace.array(rows, "exclude")),
    WWorkspace.table.go(Some{ms}, WWorkspace.array(rows, "exclude")),
    WWorkspace.Root{WWorkspace.Spec{WWorkspace.entries.of(ms), WWorkspace.paths.of(xs)}},
    Equal.cong(Maybe<&2, List<&2, String>>, WWorkspace.Read, mm => WWorkspace.table.go(mm, WWorkspace.array(rows,
        "exclude")),
      WWorkspace.array(rows, "members"), Some{ms}, em),
    Equal.cong(Maybe<&2, List<&2, String>>, WWorkspace.Read, mm => WWorkspace.table.go(Some{ms}, mm),
      WWorkspace.array(rows, "exclude"), Some{xs}, ex))

def Laws.table_refuses_members(rows, em):
  Equal.cong(Maybe<&2, List<&2, String>>, WWorkspace.Read, mm => WWorkspace.table.go(mm, WWorkspace.array(rows,
      "exclude")),
    WWorkspace.array(rows, "members"), None{}, em)

def Laws.array_at_key(key, items, rest):
  Equal.cong(Bool, Maybe<&2, List<&2, String>>, bb => WWorkspace.array.at(bb, E.VArr{items}, WWorkspace.array(rest,
      key)),
    String.eq(key, key), True{}, Eq.string_eq_self(key))

def Laws.strs_refuses_other(_bit, _rest):
  {==}
