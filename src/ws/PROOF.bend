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
import ./root.bend as R
import ./joint.bend as J
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
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

# ---------------------------------------------------------------------------
# finding the root

# by induction on where ez runs: the directories above the parent, one
# segment further down, start with the parent
def Laws.asks_nearest(here):
  match here:
    case []:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, R.Ask>, List<&2, R.Ask>,
        xs => List.append(&2, R.Ask, R.asks.under(hd, xs), [R.Ask{[], hd <> tl}]),
        R.asks(tl), R.Ask{tl, []} <> Laws.asks.rest(tl), Laws.asks_nearest(tl))

# the top is put last, at the top and with a segment in front alike
def Laws.asks_top(here):
  match here:
    case []:
      {==}
    case _hd <> _tl:
      {==}

# a path compares equal to itself, segment by segment
def segs_eq_self(ds: List<&2, String>) -> {W.segs.eq(ds, ds) == True{} : Bool}:
  match ds:
    case []:
      {==}
    case +hd <> +tl:
      Str.and_true(String.eq(hd, hd), W.segs.eq(tl, tl), Eq.string_eq_self(hd), segs_eq_self(tl))

# where the brackets of two `and`s fall does not matter
def and_assoc(
  aa: Bool,
  bb: Bool,
  cc: Bool
) -> {Bool.and(aa, Bool.and(bb, cc)) == Bool.and(Bool.and(aa, bb), cc) : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# the directories of two lists split where ez runs when those of each do
def splits_app(
  xs: List<&2, R.Ask>,
  +ys: List<&2, R.Ask>,
  +here: List<&2, String>
) -> {Laws.splits(List.append(&2, R.Ask, xs, ys), here)
    == Bool.and(Laws.splits(xs, here), Laws.splits(ys, here)) : Bool}:
  match xs:
    case []:
      {==}
    case R.Ask{+ds, +rs} <> +xt:
      Equal.trans(Bool,
        Bool.and(W.segs.eq(List.append(&2, String, ds, rs), here),
          Laws.splits(List.append(&2, R.Ask, xt, ys), here)),
        Bool.and(W.segs.eq(List.append(&2, String, ds, rs), here),
          Bool.and(Laws.splits(xt, here), Laws.splits(ys, here))),
        Bool.and(Bool.and(W.segs.eq(List.append(&2, String, ds, rs), here), Laws.splits(xt, here)),
          Laws.splits(ys, here)),
        Equal.cong(Bool, Bool, bb => Bool.and(W.segs.eq(List.append(&2, String, ds, rs), here), bb),
          Laws.splits(List.append(&2, R.Ask, xt, ys), here),
          Bool.and(Laws.splits(xt, here), Laws.splits(ys, here)),
          splits_app(xt, ys, here)),
        and_assoc(W.segs.eq(List.append(&2, String, ds, rs), here), Laws.splits(xt, here),
          Laws.splits(ys, here)))

# directories asked about from one segment further down split where ez runs
# when they split one segment further down
def splits_under(
  +hd: String,
  xs: List<&2, R.Ask>,
  +tl: List<&2, String>
) -> {Laws.splits(R.asks.under(hd, xs), hd <> tl) == Laws.splits(xs, tl) : Bool}:
  match xs:
    case []:
      {==}
    case R.Ask{+ds, +rs} <> +xt:
      Equal.trans(Bool,
        Bool.and(Bool.and(String.eq(hd, hd), W.segs.eq(List.append(&2, String, ds, rs), tl)),
          Laws.splits(R.asks.under(hd, xt), hd <> tl)),
        Bool.and(W.segs.eq(List.append(&2, String, ds, rs), tl),
          Laws.splits(R.asks.under(hd, xt), hd <> tl)),
        Bool.and(W.segs.eq(List.append(&2, String, ds, rs), tl), Laws.splits(xt, tl)),
        Equal.cong(Bool, Bool,
          bb => Bool.and(Bool.and(bb, W.segs.eq(List.append(&2, String, ds, rs), tl)),
            Laws.splits(R.asks.under(hd, xt), hd <> tl)),
          String.eq(hd, hd), True{}, Eq.string_eq_self(hd)),
        Equal.cong(Bool, Bool, bb => Bool.and(W.segs.eq(List.append(&2, String, ds, rs), tl), bb),
          Laws.splits(R.asks.under(hd, xt), hd <> tl), Laws.splits(xt, tl),
          splits_under(hd, xt, tl)))

# by induction on where ez runs: the directories above the parent split
# there, one segment further down, and the top is the whole path above it
def Laws.asks_split(here):
  match here:
    case []:
      {==}
    case +hd <> +tl:
      Equal.trans(Bool,
        Laws.splits(List.append(&2, R.Ask, R.asks.under(hd, R.asks(tl)), [R.Ask{[], hd <> tl}]), hd <> tl),
        Bool.and(Laws.splits(R.asks.under(hd, R.asks(tl)), hd <> tl),
          Laws.splits([R.Ask{[], hd <> tl}], hd <> tl)),
        True{},
        splits_app(R.asks.under(hd, R.asks(tl)), [R.Ask{[], hd <> tl}], hd <> tl),
        Str.and_true(Laws.splits(R.asks.under(hd, R.asks(tl)), hd <> tl),
          Laws.splits([R.Ask{[], hd <> tl}], hd <> tl),
          Equal.trans(Bool, Laws.splits(R.asks.under(hd, R.asks(tl)), hd <> tl),
            Laws.splits(R.asks(tl), tl), True{},
            splits_under(hd, R.asks(tl), tl), Laws.asks_split(tl)),
          Str.and_true(W.segs.eq(hd <> tl, hd <> tl), True{}, segs_eq_self(hd <> tl), {==})))

def Laws.root_skips_none(_ds, _rs, _ups):
  {==}

def Laws.root_skips_lone(ds, rs, tt, ups, ev):
  Equal.cong(W.Read, R.Found, rd => R.root.read(rd, ds, rs, R.root.go(ups)), W.spec.of(tt), W.Lone{}, ev)

def Laws.root_bad_refuses(ds, rs, tt, ups, why, ev):
  Equal.cong(W.Read, R.Found, rd => R.root.read(rd, ds, rs, R.root.go(ups)), W.spec.of(tt), W.Bad{why}, ev)

def Laws.root_claims_it(ds, rs, tt, ups, spec, ev, ec):
  Equal.trans(R.Found,
    R.root.read(W.spec.of(tt), ds, rs, R.root.go(ups)),
    R.root.claim(R.claims(spec, rs), ds, rs, R.root.go(ups)),
    R.Within{ds, rs},
    Equal.cong(W.Read, R.Found, rd => R.root.read(rd, ds, rs, R.root.go(ups)), W.spec.of(tt), W.Root{spec}, ev),
    Equal.cong(Bool, R.Found, bb => R.root.claim(bb, ds, rs, R.root.go(ups)), R.claims(spec, rs), True{}, ec))

def Laws.root_passes_by(ds, rs, tt, ups, spec, ev, ec):
  Equal.trans(R.Found,
    R.root.read(W.spec.of(tt), ds, rs, R.root.go(ups)),
    R.root.claim(R.claims(spec, rs), ds, rs, R.root.go(ups)),
    R.root.go(ups),
    Equal.cong(W.Read, R.Found, rd => R.root.read(rd, ds, rs, R.root.go(ups)), W.spec.of(tt), W.Root{spec}, ev),
    Equal.cong(Bool, R.Found, bb => R.root.claim(bb, ds, rs, R.root.go(ups)), R.claims(spec, rs), False{}, ec))

# a ledger that says nothing of a workspace leaves the search to the
# directories above
def quiet_read(
  rd: W.Read,
  +ds: List<&2, String>,
  +rs: List<&2, String>,
  rest: R.Found,
  ev: {Laws.quiet.read(rd) == True{} : Bool}
) -> {R.root.read(rd, ds, rs, rest) == rest : R.Found}:
  match rd:
    case W.Lone{}:
      {==}
    case W.Bad{why}:
      Eq.bit.absurd(&2, {R.root.read(W.Bad{why}, ds, rs, rest) == rest : R.Found}, ev)
    case W.Root{spec}:
      Eq.bit.absurd(&2, {R.root.read(W.Root{spec}, ds, rs, rest) == rest : R.Found}, ev)

# and so does a directory with no ledger
def quiet_at(
  text: Maybe<&2, String>,
  +ds: List<&2, String>,
  +rs: List<&2, String>,
  rest: R.Found,
  ev: {Laws.quiet.one(text) == True{} : Bool}
) -> {R.root.at(text, ds, rs, rest) == rest : R.Found}:
  match text:
    case None{}:
      {==}
    case Some{tt}:
      quiet_read(W.spec.of(tt), ds, rs, rest, ev)

# by induction on the directories read: each leaves the search to the rest
def Laws.root_none(ups, ev):
  match ups:
    case []:
      {==}
    case R.Up{+ds, +rs, +tx} <> +tl:
      Equal.trans(R.Found, R.root.at(tx, ds, rs, R.root.go(tl)), R.root.go(tl), R.Alone{},
        quiet_at(tx, ds, rs, R.root.go(tl), Eq.and.left(Laws.quiet.one(tx), Laws.quiet(tl), ev)),
        Laws.root_none(tl, Eq.and.right(Laws.quiet.one(tx), Laws.quiet(tl), ev)))

def Laws.claims_self(_spec):
  {==}

def Laws.claims_member(_spec, _hd, _tl):
  {==}

# ---------------------------------------------------------------------------
# one lock

def Laws.joint_lone(text, fs, ev):
  Equal.cong(W.Read, J.Joint, rd => J.joint.spec(rd, text, fs), W.spec.of(text), W.Lone{}, ev)

def Laws.lone_locks_own(_own):
  {==}

def Laws.joint_bad_table(text, fs, why, ev):
  Equal.cong(W.Read, J.Joint, rd => J.joint.spec(rd, text, fs), W.spec.of(text), W.Bad{why}, ev)

def Laws.joint_refused_members(text, fs, spec, why, ev, em):
  Equal.trans(J.Joint,
    J.joint.spec(W.spec.of(text), text, fs),
    J.joint.members(W.members(spec, W.root.of(text), J.ledgers(fs)), text, fs),
    J.Clash{why},
    Equal.cong(W.Read, J.Joint, rd => J.joint.spec(rd, text, fs), W.spec.of(text), W.Root{spec}, ev),
    Equal.cong(W.Members, J.Joint, mm => J.joint.members(mm, text, fs),
      W.members(spec, W.root.of(text), J.ledgers(fs)), W.Refused{why}, em))

def Laws.combine_when_ok(root, ms, ev):
  Equal.cong(Bool, J.Joint, bb => J.combine.go(bb, root, ms), J.ok(root, ms), True{}, ev)

def Laws.combine_refused(root, ms, ev):
  Equal.cong(Bool, J.Joint, bb => J.combine.go(bb, root, ms), J.ok(root, ms), False{}, ev)

# one dependency dropped from a list, when it is or is not of the name dropped
def without_arm(
  cc: Bool,
  +yn: String,
  +yh: String,
  +ye: String,
  +ys2: M.Source,
  +yt: List<&2, M.Dep>,
  +gone: String,
  +name: String,
  ec: {String.eq(yn, gone) == cc : Bool},
  ih: {M.find(Rend.without(yt, gone), name) == M.find(yt, name) : M.Dep},
  en: {String.eq(gone, name) == False{} : Bool}
) -> {M.find(Rend.without.put(cc, M.Dep{yn, yh, ye, ys2}, Rend.without(yt, gone)), name)
    == M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, M.find(yt, name)) : M.Dep}:
  match cc:
    case True{}:
      Equal.trans(M.Dep, M.find(Rend.without(yt, gone), name), M.find(yt, name),
        M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, M.find(yt, name)), ih,
        Equal.sym(M.Dep, M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, M.find(yt, name)),
          M.find(yt, name),
          Equal.cong(Bool, M.Dep, bb => M.find.pick(bb, M.Dep{yn, yh, ye, ys2}, M.find(yt, name)),
            String.eq(yn, name), False{},
            Equal.trans(Bool, String.eq(yn, name), String.eq(gone, name), False{},
              Equal.cong(String, Bool, ss => String.eq(ss, name), yn, gone,
                Str.string_eq_true(yn, gone, ec)), en))))
    case False{}:
      Equal.cong(M.Dep, M.Dep, dd => M.find.pick(String.eq(yn, name), M.Dep{yn, yh, ye, ys2}, dd),
        M.find(Rend.without(yt, gone), name), M.find(yt, name), ih)

# dropping another name leaves what a name finds as it was
def find_without(
  ys: List<&2, M.Dep>,
  +gone: String,
  +name: String,
  +en: {String.eq(gone, name) == False{} : Bool}
) -> {M.find(Rend.without(ys, gone), name) == M.find(ys, name) : M.Dep}:
  match ys:
    case []:
      {==}
    case M.Dep{+yn, +yh, +ye, +ys2} <> +yt:
      without_arm(String.eq(yn, gone), yn, yh, ye, ys2, yt, gone, name, {==},
        find_without(yt, gone, name, en), en)

# the first declaration in front, of the name or not
def firsts_arm(
  bb: Bool,
  +hd: M.Dep,
  +hn: String,
  +tl: List<&2, M.Dep>,
  +name: String,
  eb: {String.eq(hn, name) == bb : Bool},
  ih: {M.find(J.firsts(tl), name) == M.find(tl, name) : M.Dep}
) -> {M.find.pick(bb, hd, M.find(Rend.without(J.firsts(tl), hn), name))
    == M.find.pick(bb, hd, M.find(tl, name)) : M.Dep}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(M.Dep, M.find(Rend.without(J.firsts(tl), hn), name), M.find(J.firsts(tl), name),
        M.find(tl, name), find_without(J.firsts(tl), hn, name, eb), ih)

# by induction on the declarations: the one in front is found first in both,
# and past it the rest finds what it did
def Laws.firsts_find(ds, name):
  match ds:
    case []:
      {==}
    case M.Dep{+hn, +hh, +he, +hs} <> +tl:
      firsts_arm(String.eq(hn, name), M.Dep{hn, hh, he, hs}, hn, tl, name, {==},
        Laws.firsts_find(tl, name))

# one tool dropped from a list, when it is or is not of the name dropped
def tool_without_arm(
  cc: Bool,
  +yn: String,
  +ye: String,
  +yb: String,
  +ys2: M.Source,
  +yt: List<&2, M.Tool>,
  +gone: String,
  +name: String,
  ec: {String.eq(yn, gone) == cc : Bool},
  ih: {M.tool.find(J.tools.without(yt, gone), name) == M.tool.find(yt, name) : M.Tool},
  en: {String.eq(gone, name) == False{} : Bool}
) -> {M.tool.find(J.tools.without.put(cc, M.Tool{yn, ye, yb, ys2}, J.tools.without(yt, gone)), name)
    == M.tool.find.pick(String.eq(yn, name), M.Tool{yn, ye, yb, ys2}, M.tool.find(yt, name)) : M.Tool}:
  match cc:
    case True{}:
      Equal.trans(M.Tool, M.tool.find(J.tools.without(yt, gone), name), M.tool.find(yt, name),
        M.tool.find.pick(String.eq(yn, name), M.Tool{yn, ye, yb, ys2}, M.tool.find(yt, name)), ih,
        Equal.sym(M.Tool, M.tool.find.pick(String.eq(yn, name), M.Tool{yn, ye, yb, ys2}, M.tool.find(yt, name)),
          M.tool.find(yt, name),
          Equal.cong(Bool, M.Tool, bb => M.tool.find.pick(bb, M.Tool{yn, ye, yb, ys2}, M.tool.find(yt, name)),
            String.eq(yn, name), False{},
            Equal.trans(Bool, String.eq(yn, name), String.eq(gone, name), False{},
              Equal.cong(String, Bool, ss => String.eq(ss, name), yn, gone,
                Str.string_eq_true(yn, gone, ec)), en))))
    case False{}:
      Equal.cong(M.Tool, M.Tool, dd => M.tool.find.pick(String.eq(yn, name), M.Tool{yn, ye, yb, ys2}, dd),
        M.tool.find(J.tools.without(yt, gone), name), M.tool.find(yt, name), ih)

# dropping another name leaves what a name finds among the tools as it was
def tool_find_without(
  ys: List<&2, M.Tool>,
  +gone: String,
  +name: String,
  +en: {String.eq(gone, name) == False{} : Bool}
) -> {M.tool.find(J.tools.without(ys, gone), name) == M.tool.find(ys, name) : M.Tool}:
  match ys:
    case []:
      {==}
    case M.Tool{+yn, +ye, +yb, +ys2} <> +yt:
      tool_without_arm(String.eq(yn, gone), yn, ye, yb, ys2, yt, gone, name, {==},
        tool_find_without(yt, gone, name, en), en)

# the first tool in front, of the name or not
def tools_firsts_arm(
  bb: Bool,
  +hd: M.Tool,
  +hn: String,
  +tl: List<&2, M.Tool>,
  +name: String,
  eb: {String.eq(hn, name) == bb : Bool},
  ih: {M.tool.find(J.tools.firsts(tl), name) == M.tool.find(tl, name) : M.Tool}
) -> {M.tool.find.pick(bb, hd, M.tool.find(J.tools.without(J.tools.firsts(tl), hn), name))
    == M.tool.find.pick(bb, hd, M.tool.find(tl, name)) : M.Tool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(M.Tool, M.tool.find(J.tools.without(J.tools.firsts(tl), hn), name),
        M.tool.find(J.tools.firsts(tl), name), M.tool.find(tl, name),
        tool_find_without(J.tools.firsts(tl), hn, name, eb), ih)

def Laws.tools_firsts_find(ts, name):
  match ts:
    case []:
      {==}
    case M.Tool{+hn, +he, +hb, +hs} <> +tl:
      tools_firsts_arm(String.eq(hn, name), M.Tool{hn, he, hb, hs}, hn, tl, name, {==},
        Laws.tools_firsts_find(tl, name))

def Laws.combine_needs_hub(root, ms, ev):
  Eq.and.left(J.hubs(J.root.hub(root), ms),
    Bool.and(J.agree(J.all.deps(root, ms)), J.tools.agree(J.all.tools(root, ms))), ev)

def Laws.combine_needs_deps(root, ms, ev):
  Eq.and.left(J.agree(J.all.deps(root, ms)), J.tools.agree(J.all.tools(root, ms)),
    Eq.and.right(J.hubs(J.root.hub(root), ms),
      Bool.and(J.agree(J.all.deps(root, ms)), J.tools.agree(J.all.tools(root, ms))), ev))

def Laws.combine_needs_tools(root, ms, ev):
  Eq.and.right(J.agree(J.all.deps(root, ms)), J.tools.agree(J.all.tools(root, ms)),
    Eq.and.right(J.hubs(J.root.hub(root), ms),
      Bool.and(J.agree(J.all.deps(root, ms)), J.tools.agree(J.all.tools(root, ms))), ev))

# ---------------------------------------------------------------------------
# where a whole-workspace command runs

def Laws.hop_alone(_top):
  {==}

def Laws.hop_at_root(_top, _root):
  {==}

def Laws.hop_member(_top, _root, _hd, _tl):
  {==}

def Laws.hop_broken(_top, _why):
  {==}

def Laws.hop_keeps_words(_dir, _pwd, _prog, _words):
  {==}
