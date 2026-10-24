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
import 0xc5d9d3e28b79ea98be22eb42c7e37802/main.bend as E
import ./root.bend as R
import ./joint.bend as J
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../pkg/pkg.bend as K
import ../lock/lock.bend as L
import ../ledger/ignore.bend as I
import ../toml/toml.bend as T
import ../pub/plan.bend as PP
import ./up.bend as U
import ./moved.bend as Mv
import ./doctor.bend as Doc
import ../doctor/plan.bend as DP
import ../doctor/world.bend as DW
import ../doctor/PROOF.bend as DPF
import ../doctor/LAWS.bend as DL
import ../ledger/upgrade.bend as LU
import ./pin.bend as Pin
import ../ez/target.bend as Tgt
import ../lock/world.bend as LW
import ../lock/plan.bend as LP
import ../lock/LAWS.bend as LL
import ../lock/PROOF.bend as LPF
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

def Laws.joint_lone(text, fs, files, ev):
  Equal.cong(W.Read, J.Joint, rd => J.joint.spec(rd, text, fs, files), W.spec.of(text), W.Lone{}, ev)

def Laws.lone_locks_own(_own):
  {==}

def Laws.joint_bad_table(text, fs, files, why, ev):
  Equal.cong(W.Read, J.Joint, rd => J.joint.spec(rd, text, fs, files), W.spec.of(text), W.Bad{why}, ev)

def Laws.joint_refused_members(text, fs, files, spec, why, ev, em):
  Equal.trans(J.Joint,
    J.joint.spec(W.spec.of(text), text, fs, files),
    J.joint.members(W.members(spec, W.root.of(text), J.ledgers(fs)), text, fs, files),
    J.Clash{why},
    Equal.cong(W.Read, J.Joint, rd => J.joint.spec(rd, text, fs, files), W.spec.of(text), W.Root{spec}, ev),
    Equal.cong(W.Members, J.Joint, mm => J.joint.members(mm, text, fs, files),
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
    Bool.and(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
      J.tools.agree(J.all.tools(root, ms))), ev)

# what is left of a join once its hub is taken off
def join.rest(
  +root: M.Manifest,
  +ms: List<&2, J.Member>,
  +ev: {J.ok(root, ms) == True{} : Bool}
) -> {Bool.and(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
    J.tools.agree(J.all.tools(root, ms))) == True{} : Bool}:
  Eq.and.right(J.hubs(J.root.hub(root), ms),
    Bool.and(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
      J.tools.agree(J.all.tools(root, ms))), ev)

# and its dependencies' half
def join.deps(
  +root: M.Manifest,
  +ms: List<&2, J.Member>,
  +ev: {J.ok(root, ms) == True{} : Bool}
) -> {Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))) == True{} : Bool}:
  Eq.and.left(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
    J.tools.agree(J.all.tools(root, ms)), join.rest(root, ms, ev))

def Laws.combine_needs_deps(root, ms, ev):
  Eq.and.left(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms)), join.deps(root, ms, ev))

def Laws.combine_needs_pins(root, ms, ev):
  Eq.and.right(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms)), join.deps(root, ms, ev))

def Laws.combine_needs_tools(root, ms, ev):
  Eq.and.right(Bool.and(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms))),
    J.tools.agree(J.all.tools(root, ms)), join.rest(root, ms, ev))

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

# ---------------------------------------------------------------------------
# one pin per source

def Laws.up_alone(_world):
  {==}

# a workspace's plan under a plain lock is the planner's, when no line is
# stale
def up_plain_at(
  up: Bool,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +lock: String,
  +world: LW.World,
  ev: {up == False{} : Bool},
  es: {U.stale.at(up, lock, world) == "" : String}
) -> {U.plan.at(up, U.Back{text, spec, fs, lock}, world) == LP.plan(world) : LP.Plan}:
  match up:
    case True{}:
      Eq.bit.absurd2(&2, {U.plan.at(True{}, U.Back{text, spec, fs, lock}, world) == LP.plan(world) : LP.Plan}, ev)
    case False{}:
      %Equal.sym(String, Mv.stale.world(lock, world), "", es)
        : {U.plan.plain(String.is_empty(_), _, world) == LP.plan(world) : LP.Plan}
      {==}

def Laws.up_plain(back, world, ev, es):
  match back:
    case U.Alone{}:
      {==}
    case U.Back{+text, +spec, +fs, +lock}:
      up_plain_at(LW.args.upgrade(world), text, spec, fs, lock, world, ev, es)

def Laws.pin_back(nn, _hh, _ee, url, _rev, _tag, _root, _nar, vend, js, jn, jh, je, ju, jr, jt, jo, jnar, jv, ev):
  Equal.cong(M.Dep, M.Dep, dd => U.dep.back.at(M.Dep{nn, _hh, _ee, M.Git{url, _rev, _tag, _root, _nar, vend}}, dd),
    M.find(js, nn), M.Dep{jn, jh, je, M.Git{ju, jr, jt, jo, jnar, jv}}, ev)

def Laws.tool_pin_back(nn, ee, bb, url, _rev, _tag, _root, _nar, vend, ts, jn, je, jb, ju, jr, jt, jo, jnar, jv, ev):
  Equal.cong(M.Tool, M.Tool,
    dd => U.tool.back.at(M.Tool{nn, ee, bb, M.Git{url, _rev, _tag, _root, _nar, vend}}, dd),
    M.tool.find(ts, nn), M.Tool{jn, je, jb, M.Git{ju, jr, jt, jo, jnar, jv}}, ev)

# effects that write nothing write nothing once the ledgers' writes take the
# place of ez.toml's, since there was no write of ez.toml to replace
def back_writes_none(
  es: List<&2, LP.Effect>,
  +ws: List<&2, LP.Effect>,
  +ev: {LP.writes.in(es) == False{} : Bool}
) -> {LP.writes.in(U.effects.back(es, ws)) == False{} : Bool}:
  match es:
    case []:
      {==}
    case LP.Write{at, text} <> tl:
      Eq.bit.absurd2(&2, {LP.writes.in(U.effects.back(LP.Write{at, text} <> tl, ws)) == False{} : Bool}, ev)
    case LP.Lay{pl, hash, files} <> tl:
      Eq.bit.absurd2(&2, {LP.writes.in(U.effects.back(LP.Lay{pl, hash, files} <> tl, ws)) == False{} : Bool}, ev)
    case LP.Drop{hash} <> tl:
      Eq.bit.absurd2(&2, {LP.writes.in(U.effects.back(LP.Drop{hash} <> tl, ws)) == False{} : Bool}, ev)
    case LP.Say{_text} <> +tl:
      back_writes_none(tl, ws, ev)
    case LP.Name{nv, hash} <> tl:
      Eq.bit.absurd2(&2, {LP.writes.in(U.effects.back(LP.Name{nv, hash} <> tl, ws)) == False{} : Bool}, ev)

# and so for a plan
def back_plan_writes_none(
  pl: LP.Plan,
  +ws: List<&2, LP.Effect>,
  +ev: {LP.writes(pl) == False{} : Bool}
) -> {LP.writes(U.plan.back(pl, ws)) == False{} : Bool}:
  match pl:
    case LP.Plan{es, _outcome}:
      back_writes_none(es, ws, ev)

# a plain lock's plan on a World that refuses writes nothing, whether a
# line is stale or not
def plain_refused(
  fine: Bool,
  +why: String,
  +world: LW.World,
  +er: {LP.refuses(world) == True{} : Bool}
) -> {LP.writes(U.plan.plain(fine, why, world)) == False{} : Bool}:
  match fine:
    case True{}:
      LL.lock_refusal_writes_nothing(world, er)
    case False{}:
      {==}

# a workspace's plan that refuses writes nothing, upgrade or not
def up_refused_at(
  up: Bool,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +lock: String,
  +world: LW.World,
  +er: {LP.refuses(U.world.at(up, text, fs, lock, world)) == True{} : Bool}
) -> {LP.writes(U.plan.at(up, U.Back{text, spec, fs, lock}, world)) == False{} : Bool}:
  match up:
    case True{}:
      +w2 = U.up.world(U.up.of(text, fs, lock, world))
      %Equal.sym(Bool, LP.refuses(w2), True{}, er)
        : {LP.writes(U.edits.put(_, Mv.edits(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, U.files.of(world), lock,
            LW.args.only(world)))), U.files.of(world)),
          U.plan.back(LP.plan(w2), U.writes(U.Back{text, spec, fs, lock}, LP.ledger.next(w2)))))
          == False{} : Bool}
      back_plan_writes_none(LP.plan(w2), U.writes(U.Back{text, spec, fs, lock}, LP.ledger.next(w2)),
        LL.lock_refusal_writes_nothing(w2, er))
    case False{}:
      plain_refused(String.is_empty(Mv.stale.world(lock, world)), Mv.stale.world(lock, world), world, er)

def Laws.up_refusal_writes_nothing(back, world, er):
  match back:
    case U.Alone{}:
      LL.lock_refusal_writes_nothing(world, er)
    case U.Back{+text, +spec, +fs, +lock}:
      up_refused_at(LW.args.upgrade(world), text, spec, fs, lock, world, er)

# whether no effect of a list writes at a path
def misses(es: List<&2, LP.Effect>, +path: String) -> Bool:
  match es:
    case []:
      True{}
    case LP.Write{at, _text} <> tl:
      Bool.and(Bool.not(String.eq(at, path)), misses(tl, path))
    case _hd <> tl:
      misses(tl, path)

# a write elsewhere leaves what the effects after it leave at a path
def put_one_miss(
  +at: String,
  text: String,
  +path: String,
  rest: LP.Wrote,
  ev: {String.eq(at, path) == False{} : Bool}
) -> {LP.put.one(LP.Write{at, text}, path, rest) == rest : LP.Wrote}:
  match rest:
    case LP.Kept{}:
      Equal.cong(Bool, LP.Wrote, bb => Bool.pick(LP.Wrote, bb, LP.Put{text}, LP.Kept{}),
        String.eq(at, path), False{}, ev)
    case LP.Put{_later}:
      {==}

# writes that miss a path, put in front, leave it as what follows leaves it
def app_misses(
  ws: List<&2, LP.Effect>,
  +rest: List<&2, LP.Effect>,
  +path: String,
  +ev: {misses(ws, path) == True{} : Bool}
) -> {LP.put.in(List.append(&2, LP.Effect, ws, rest), path) == LP.put.in(rest, path) : LP.Wrote}:
  match ws:
    case []:
      {==}
    case LP.Write{+at, +text} <> +tl:
      Equal.trans(LP.Wrote,
        LP.put.one(LP.Write{at, text}, path, LP.put.in(List.append(&2, LP.Effect, tl, rest), path)),
        LP.put.in(List.append(&2, LP.Effect, tl, rest), path),
        LP.put.in(rest, path),
        put_one_miss(at, text, path, LP.put.in(List.append(&2, LP.Effect, tl, rest), path),
          Eq.not.true(String.eq(at, path),
            Eq.and.left(Bool.not(String.eq(at, path)), misses(tl, path), ev))),
        app_misses(tl, rest, path, Eq.and.right(Bool.not(String.eq(at, path)), misses(tl, path), ev)))
    case LP.Lay{_pl, _hash, _files} <> +tl:
      app_misses(tl, rest, path, ev)
    case LP.Drop{_hash} <> +tl:
      app_misses(tl, rest, path, ev)
    case LP.Say{_text} <> +tl:
      app_misses(tl, rest, path, ev)
    case LP.Name{_nv, _hash} <> +tl:
      app_misses(tl, rest, path, ev)

# a write kept, or the ledgers' in place of ez.toml's, leaves the lock as the
# plan left it
def write_back_lock(
  hit: Bool,
  +at: String,
  +text: String,
  +ws: List<&2, LP.Effect>,
  +tl: List<&2, LP.Effect>,
  eh: {String.eq(at, "ez.toml") == hit : Bool},
  +ev: {misses(ws, LP.lockfile()) == True{} : Bool},
  ih: {LP.put.in(U.effects.back(tl, ws), LP.lockfile()) == LP.put.in(tl, LP.lockfile()) : LP.Wrote}
) -> {LP.put.in(U.effect.write(hit, at, text, ws, U.effects.back(tl, ws)), LP.lockfile())
    == LP.put.one(LP.Write{at, text}, LP.lockfile(), LP.put.in(tl, LP.lockfile())) : LP.Wrote}:
  match hit:
    case True{}:
      Equal.trans(LP.Wrote,
        LP.put.in(List.append(&2, LP.Effect, ws, U.effects.back(tl, ws)), LP.lockfile()),
        LP.put.in(tl, LP.lockfile()),
        LP.put.one(LP.Write{at, text}, LP.lockfile(), LP.put.in(tl, LP.lockfile())),
        Equal.trans(LP.Wrote,
          LP.put.in(List.append(&2, LP.Effect, ws, U.effects.back(tl, ws)), LP.lockfile()),
          LP.put.in(U.effects.back(tl, ws), LP.lockfile()),
          LP.put.in(tl, LP.lockfile()),
          app_misses(ws, U.effects.back(tl, ws), LP.lockfile(), ev), ih),
        Equal.sym(LP.Wrote,
          LP.put.one(LP.Write{at, text}, LP.lockfile(), LP.put.in(tl, LP.lockfile())),
          LP.put.in(tl, LP.lockfile()),
          put_one_miss(at, text, LP.lockfile(), LP.put.in(tl, LP.lockfile()),
            Equal.cong(String, Bool, ss => String.eq(ss, LP.lockfile()), at, "ez.toml",
              Str.string_eq_true(at, "ez.toml", eh)))))
    case False{}:
      Equal.cong(LP.Wrote, LP.Wrote, rr => LP.put.one(LP.Write{at, text}, LP.lockfile(), rr),
        LP.put.in(U.effects.back(tl, ws), LP.lockfile()), LP.put.in(tl, LP.lockfile()), ih)

# by induction on the effects: each is kept, or is the write of ez.toml,
# which the ledgers' writes replace and none of which is the lock's
def effects_back_lock(
  es: List<&2, LP.Effect>,
  +ws: List<&2, LP.Effect>,
  +ev: {misses(ws, LP.lockfile()) == True{} : Bool}
) -> {LP.put.in(U.effects.back(es, ws), LP.lockfile()) == LP.put.in(es, LP.lockfile()) : LP.Wrote}:
  match es:
    case []:
      {==}
    case LP.Write{+at, +text} <> +tl:
      write_back_lock(String.eq(at, "ez.toml"), at, text, ws, tl, {==}, ev, effects_back_lock(tl, ws, ev))
    case LP.Lay{_pl, _hash, _files} <> +tl:
      effects_back_lock(tl, ws, ev)
    case LP.Drop{_hash} <> +tl:
      effects_back_lock(tl, ws, ev)
    case LP.Say{_text} <> +tl:
      effects_back_lock(tl, ws, ev)
    case LP.Name{_nv, _hash} <> +tl:
      effects_back_lock(tl, ws, ev)

# the two halves of a list of writes miss a path when each does
def misses_app(
  as: List<&2, LP.Effect>,
  +bs: List<&2, LP.Effect>,
  +path: String,
  +ea: {misses(as, path) == True{} : Bool},
  eb: {misses(bs, path) == True{} : Bool}
) -> {misses(List.append(&2, LP.Effect, as, bs), path) == True{} : Bool}:
  match as:
    case []:
      eb
    case LP.Write{+at, _text} <> +tl:
      Str.and_true(Bool.not(String.eq(at, path)), misses(List.append(&2, LP.Effect, tl, bs), path),
        Eq.and.left(Bool.not(String.eq(at, path)), misses(tl, path), ea),
        misses_app(tl, bs, path, Eq.and.right(Bool.not(String.eq(at, path)), misses(tl, path), ea), eb))
    case LP.Lay{_pl, _hash, _files} <> +tl:
      misses_app(tl, bs, path, ea, eb)
    case LP.Drop{_hash} <> +tl:
      misses_app(tl, bs, path, ea, eb)
    case LP.Say{_text} <> +tl:
      misses_app(tl, bs, path, ea, eb)
    case LP.Name{_nv, _hash} <> +tl:
      misses_app(tl, bs, path, ea, eb)

# a ledger written back, or not, misses the lock when its path is not the
# lock's
def pick_miss(
  bb: Bool,
  +at: String,
  text: String,
  ev: {String.eq(at, LP.lockfile()) == False{} : Bool}
) -> {misses(Bool.pick(List<&2, LP.Effect>, bb, [], [LP.Write{at, text}]), LP.lockfile()) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, Bool, xx => Bool.and(Bool.not(xx), True{}), String.eq(at, LP.lockfile()), False{}, ev)

# a member's ledger is not the lock: its path holds a `/`
def member_not_lock(
  hit: Bool,
  +pre: String,
  eh: {String.eq(pre ++ "/ez.toml", LP.lockfile()) == hit : Bool}
) -> {String.eq(pre ++ "/ez.toml", LP.lockfile()) == False{} : Bool}:
  match hit:
    case False{}:
      eh
    case True{}:
      Eq.bit.absurd2(&2, {String.eq(pre ++ "/ez.toml", LP.lockfile()) == False{} : Bool},
        Equal.trans(Bool, True{}, Str.clear(pre ++ "/ez.toml", '/'), False{},
          Equal.sym(Bool, Str.clear(pre ++ "/ez.toml", '/'), True{},
            Equal.cong(String, Bool, ss => Str.clear(ss, '/'), pre ++ "/ez.toml", LP.lockfile(),
              Str.string_eq_true(pre ++ "/ez.toml", LP.lockfile(), eh))),
          LPF.slash_member(pre)))

# a member's ledger written back misses the lock
def member_write_miss(
  rd: M.Read,
  +ds: List<&2, String>,
  +joint: M.Manifest
) -> {misses(U.member.write(rd, ds, joint), LP.lockfile()) == True{} : Bool}:
  match rd:
    case M.Bad{_why}:
      {==}
    case M.Good{+mm}:
      pick_miss(String.eq(Rend.show(mm), Rend.show(U.ledger.back(mm, joint))),
        W.segs.text(ds) ++ "/ez.toml", Rend.show(U.ledger.back(mm, joint)),
        member_not_lock(String.eq(W.segs.text(ds) ++ "/ez.toml", LP.lockfile()), W.segs.text(ds), {==}))

# a member's, kept or passed by
def found_pick_miss(
  bb: Bool,
  +text: String,
  +ds: List<&2, String>,
  +joint: M.Manifest
) -> {misses(U.found.pick(bb, text, ds, joint), LP.lockfile()) == True{} : Bool}:
  match bb:
    case True{}:
      member_write_miss(M.parse(text), ds, joint)
    case False{}:
      {==}

# one ez.toml git listed, written back or not, misses the lock
def found_write_miss(
  lg: Maybe<&2, W.Ledger>,
  +text: String,
  +dirs: List<&2, List<&2, String>>,
  +joint: M.Manifest
) -> {misses(U.found.write(lg, text, dirs, joint), LP.lockfile()) == True{} : Bool}:
  match lg:
    case None{}:
      {==}
    case Some{W.Ledger{+ds, nn, ww}}:
      found_pick_miss(W.has(dirs, ds), text, ds, joint)

# every member's ledger written back misses the lock
def members_write_miss(
  fs: List<&2, J.Found>,
  +dirs: List<&2, List<&2, String>>,
  +joint: M.Manifest
) -> {misses(U.members.write(fs, dirs, joint), LP.lockfile()) == True{} : Bool}:
  match fs:
    case []:
      {==}
    case J.Found{+pp, +tt} <> +tl:
      misses_app(U.found.write(W.ledger.of(pp, tt), tt, dirs, joint), U.members.write(tl, dirs, joint),
        LP.lockfile(), found_write_miss(W.ledger.of(pp, tt), tt, dirs, joint),
        members_write_miss(tl, dirs, joint))

# the root's ledger written back misses the lock: it is ez.toml
def root_write_miss(
  rd: M.Read,
  +spec: W.Spec,
  +root: W.Root,
  +joint: M.Manifest
) -> {misses(U.root.write(rd, spec, root, joint), LP.lockfile()) == True{} : Bool}:
  match rd:
    case M.Bad{_why}:
      {==}
    case M.Good{+mm}:
      pick_miss(String.eq(Rend.show(mm), Rend.show(U.ledger.back(mm, joint))), "ez.toml",
        U.root.text(U.ledger.back(mm, joint), spec, root), {==})

# every ledger written back misses the lock, once the member set is known
def members_miss(
  ms: W.Members,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +joint: M.Manifest
) -> {misses(U.writes.members(ms, text, spec, fs, joint), LP.lockfile()) == True{} : Bool}:
  match ms:
    case W.Refused{_why}:
      {==}
    case W.Members{_root, +dirs}:
      misses_app(U.root.write(M.parse(text), spec, W.root.of(text), joint), U.members.write(fs, dirs, joint),
        LP.lockfile(), root_write_miss(M.parse(text), spec, W.root.of(text), joint),
        members_write_miss(fs, dirs, joint))

# and once the joint ledger was read
def joint_miss(
  joint: M.Read,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>
) -> {misses(U.writes.joint(joint, text, spec, fs), LP.lockfile()) == True{} : Bool}:
  match joint:
    case M.Bad{_why}:
      {==}
    case M.Good{+jm}:
      members_miss(W.members(spec, W.root.of(text), J.ledgers(fs)), text, spec, fs, jm)

# a plan with the ledgers' writes in place of ez.toml's leaves the lock as it
# was
def up_lock_plan(
  pl: LP.Plan,
  +ws: List<&2, LP.Effect>,
  +ev: {misses(ws, LP.lockfile()) == True{} : Bool}
) -> {LP.put.plan(U.plan.back(pl, ws), LP.lockfile()) == LP.put.plan(pl, LP.lockfile()) : LP.Wrote}:
  match pl:
    case LP.Plan{es, _outcome}:
      effects_back_lock(es, ws, ev)

# effects that write nothing at a path, ahead of others, leave what the
# others leave there
def put_skip(
  eds: List<&2, LP.Effect>,
  +es: List<&2, LP.Effect>,
  +path: String,
  +em: {misses(eds, path) == True{} : Bool}
) -> {LP.put.in(List.append(&2, LP.Effect, eds, es), path) == LP.put.in(es, path) : LP.Wrote}:
  match eds:
    case []:
      {==}
    case LP.Write{+at, +text} <> +tl:
      +rest = put_skip(tl, es, path, Eq.and.right(Bool.not(String.eq(at, path)), misses(tl, path), em))
      Equal.trans(LP.Wrote,
        LP.put.one(LP.Write{at, text}, path, LP.put.in(List.append(&2, LP.Effect, tl, es), path)),
        LP.put.one(LP.Write{at, text}, path, LP.put.in(es, path)),
        LP.put.in(es, path),
        Equal.cong(LP.Wrote, LP.Wrote, w => LP.put.one(LP.Write{at, text}, path, w),
          LP.put.in(List.append(&2, LP.Effect, tl, es), path), LP.put.in(es, path), rest),
        put_one_miss(at, text, path, LP.put.in(es, path),
          Eq.not.true(String.eq(at, path), Eq.and.left(Bool.not(String.eq(at, path)), misses(tl, path), em))))
    case LP.Lay{_pl, _hash, _files} <> +tl:
      put_skip(tl, es, path, em)
    case LP.Drop{_hash} <> +tl:
      put_skip(tl, es, path, em)
    case LP.Say{_text} <> +tl:
      put_skip(tl, es, path, em)
    case LP.Name{_nv, _hash} <> +tl:
      put_skip(tl, es, path, em)

# a rewritten file's write, once it is known whether it would land on the lock
def edit_pick_miss(
  hit: Bool,
  +at: String,
  +text: String,
  +rest: List<&2, LP.Effect>,
  eh: {String.eq(at, LP.lockfile()) == hit : Bool},
  +er: {misses(rest, LP.lockfile()) == True{} : Bool}
) -> {misses(Bool.pick(List<&2, LP.Effect>, hit, rest, LP.Write{at, text} <> rest), LP.lockfile()) == True{} : Bool}:
  match hit:
    case True{}:
      er
    case False{}:
      %Equal.sym(Bool, String.eq(at, LP.lockfile()), False{}, eh)
        : {Bool.and(Bool.not(_), misses(rest, LP.lockfile())) == True{} : Bool}
      er

# a rewritten file's write misses the lock, changed or not
def edit_miss(
  changed: Bool,
  +at: String,
  +text: String,
  +rest: List<&2, LP.Effect>,
  +er: {misses(rest, LP.lockfile()) == True{} : Bool}
) -> {misses(Mv.edit.put(changed, at, text, rest), LP.lockfile()) == True{} : Bool}:
  match changed:
    case True{}:
      edit_pick_miss(String.eq(at, LP.lockfile()), at, text, rest, {==}, er)
    case False{}:
      er

# the files the moves rewrite never write the lock
def edits_miss(
  +ss: List<&2, LU.Swap>,
  fs: List<&2, K.Source>
) -> {misses(Mv.edits(ss, fs), LP.lockfile()) == True{} : Bool}:
  match fs:
    case []:
      {==}
    case K.Source{+at, +text} <> +tl:
      edit_miss(Bool.not(String.eq(LU.reimport.many(ss, text), text)), at, LU.reimport.many(ss, text),
        Mv.edits(ss, tl), edits_miss(ss, tl))

# the files an upgrade rewrites, put ahead of a plan, leave its lock as it was
def edits_put_lock(
  refuses: Bool,
  +eds: List<&2, LP.Effect>,
  pl: LP.Plan,
  +em: {misses(eds, LP.lockfile()) == True{} : Bool}
) -> {LP.put.plan(U.edits.put(refuses, eds, pl), LP.lockfile()) == LP.put.plan(pl, LP.lockfile()) : LP.Wrote}:
  match refuses:
    case True{}:
      {==}
    case False{}:
      match pl:
        case LP.Plan{+es, _outcome}:
          put_skip(eds, es, LP.lockfile(), em)

# a workspace's plan writes the lock its planner does on the World it plans
# on, upgrade or not
def up_lock_at(
  up: Bool,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +lock: String,
  +world: LW.World,
  es: {U.stale.at(up, lock, world) == "" : String}
) -> {LP.put.plan(U.plan.at(up, U.Back{text, spec, fs, lock}, world), LP.lockfile())
    == LP.put(U.world.at(up, text, fs, lock, world), LP.lockfile()) : LP.Wrote}:
  match up:
    case True{}:
      +w2 = U.up.world(U.up.of(text, fs, lock, world))
      +ss = Mv.swaps(Mv.cascade(Mv.ctx(text, fs, U.files.of(world), lock, LW.args.only(world))))
      +pb = U.plan.back(LP.plan(w2), U.writes(U.Back{text, spec, fs, lock}, LP.ledger.next(w2)))
      Equal.trans(LP.Wrote,
        LP.put.plan(U.edits.put(LP.refuses(w2), Mv.edits(ss, U.files.of(world)), pb), LP.lockfile()),
        LP.put.plan(pb, LP.lockfile()),
        LP.put(w2, LP.lockfile()),
        edits_put_lock(LP.refuses(w2), Mv.edits(ss, U.files.of(world)), pb, edits_miss(ss, U.files.of(world))),
        up_lock_plan(LP.plan(w2), U.writes(U.Back{text, spec, fs, lock}, LP.ledger.next(w2)),
          joint_miss(LP.ledger.next(w2), text, spec, fs)))
    case False{}:
      %Equal.sym(String, Mv.stale.world(lock, world), "", es)
        : {LP.put.plan(U.plan.plain(String.is_empty(_), _, world), LP.lockfile())
          == LP.put(world, LP.lockfile()) : LP.Wrote}
      {==}

def Laws.up_writes_the_lock(back, world, es):
  match back:
    case U.Alone{}:
      {==}
    case U.Back{+text, +spec, +fs, +lock}:
      up_lock_at(LW.args.upgrade(world), text, spec, fs, lock, world, es)

def Laws.ref_unpinned(_nv, _url, _ref):
  {==}

def Laws.ref_takes_tag(_url, _ju, _rev, _ch, _tt, _jo, _jn, _jv):
  {==}

def Laws.ref_takes_rev(_url, _ju, _rev, _jo, _jn, _jv):
  {==}

# the tag compares equal to itself, so it is the pin
def Laws.ref_keeps_pin(url, _ju, rev, ch, tt, _jo, _jn, _jv):
  Equal.cong(Bool, Pin.Ref,
    bb => Bool.pick(Pin.Ref, bb, Pin.Given{SCon{ch, tt}},
      Pin.Held{"ez: the workspace pins " ++ url ++ " at " ++ Pin.held(rev, SCon{ch, tt}) ++
        "; move it for every member with ez lock --upgrade --package"}),
    Bool.or(String.eq(SCon{ch, tt}, SCon{ch, tt}), String.eq(SCon{ch, tt}, rev)), True{},
    Equal.cong(Bool, Bool, bb => Bool.or(bb, String.eq(SCon{ch, tt}, rev)),
      String.eq(SCon{ch, tt}, SCon{ch, tt}), True{}, Eq.string_eq_self(SCon{ch, tt})))

# neither the tag nor the commit, so the ref is held
def Laws.ref_holds_other(url, _ju, rev, tag, _jo, _jn, _jv, rc, rt, et, er):
  Equal.cong(Bool, Pin.Ref,
    bb => Bool.pick(Pin.Ref, bb, Pin.Given{SCon{rc, rt}},
      Pin.Held{"ez: the workspace pins " ++ url ++ " at " ++ Pin.held(rev, tag) ++
        "; move it for every member with ez lock --upgrade --package"}),
    Bool.or(String.eq(SCon{rc, rt}, tag), String.eq(SCon{rc, rt}, rev)), False{},
    Equal.trans(Bool, Bool.or(String.eq(SCon{rc, rt}, tag), String.eq(SCon{rc, rt}, rev)),
      Bool.or(False{}, String.eq(SCon{rc, rt}, rev)), False{},
      Equal.cong(Bool, Bool, bb => Bool.or(bb, String.eq(SCon{rc, rt}, rev)),
        String.eq(SCon{rc, rt}, tag), False{}, et), er))

def Laws.ref_named_free(pins, dir, home, target, ref, ev):
  Equal.cong(Bool, Pin.Ref,
    bb => Bool.pick(Pin.Ref, bb, Pin.Given{ref}, Pin.ref.place(Tgt.classify(target), pins, dir, home, ref)),
    Tgt.aim.named(Tgt.aim(target)), True{}, ev)

def Laws.lib_keeps_env(_top, _found, _ch, _tt):
  {==}

def Laws.lib_member(_top, _root, _hd, _tl):
  {==}

def Laws.lib_own(_top, _root):
  {==}

def Laws.lib_alone(_top):
  {==}

def Laws.lib_keeps_words(_lib, _pwd, _prog, _words):
  {==}

def Laws.lock_member(_top, _root, _hd, _tl):
  {==}

def Laws.lock_own(_top, _root):
  {==}

# ---------------------------------------------------------------------------
# reading the `[workspace]` table

def Laws.spec_finds_table(_path, _sub, _rest):
  {==}

def Laws.spec_none_lone(_path, sub, ch, tt, rest, ev):
  Equal.cong(Bool, W.Read, bb => W.spec.at(bb, sub, W.spec.rows(rest)),
    String.eq(SCon{ch, tt}, "workspace"), False{}, ev)

def Laws.table_reads(rows, ms, xs, em, ex):
  Equal.trans(W.Read,
    W.table.go(W.array(rows, "members"), W.array(rows, "exclude")),
    W.table.go(Some{ms}, W.array(rows, "exclude")),
    W.Root{W.Spec{W.entries.of(ms), W.paths.of(xs)}},
    Equal.cong(Maybe<&2, List<&2, String>>, W.Read, mm => W.table.go(mm, W.array(rows, "exclude")),
      W.array(rows, "members"), Some{ms}, em),
    Equal.cong(Maybe<&2, List<&2, String>>, W.Read, mm => W.table.go(Some{ms}, mm),
      W.array(rows, "exclude"), Some{xs}, ex))

def Laws.table_refuses_members(rows, em):
  Equal.cong(Maybe<&2, List<&2, String>>, W.Read, mm => W.table.go(mm, W.array(rows, "exclude")),
    W.array(rows, "members"), None{}, em)

def Laws.array_at_key(key, items, rest):
  Equal.cong(Bool, Maybe<&2, List<&2, String>>, bb => W.array.at(bb, E.VArr{items}, W.array(rest, key)),
    String.eq(key, key), True{}, Eq.string_eq_self(key))

def Laws.strs_refuses_other(_bit, _rest):
  {==}

# ---------------------------------------------------------------------------
# a member as a dependency

def Laws.member_dep_walked(
  name,
  ms,
  self,
  files,
  dir,
  nn,
  ee,
  bb,
  hh,
  pa,
  pv,
  ds,
  ts,
  hash,
  root,
  fs,
  sums,
  ef,
  eo,
  en,
  ew
):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds,
      ts}}}, ef)
    : {J.target(_, self, name, files) == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}
  %Equal.sym(Bool, W.segs.eq(dir, self), False{}, eo)
    : {J.target.at(_, name, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}, dir, files, self) == J.Got{M.Dep{name,
        hash, J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByHash{}, en)
    : {J.by.name(_, K.of(J.entry.at(dir, ee), files), name, J.entry.at(dir, ee)) == J.Got{M.Dep{name, hash,
        J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}
  %Equal.sym(K.Walked, K.of(J.entry.at(dir, ee), files), K.Walked{hash, root, fs, sums}, ew)
    : {J.walked(_, name, J.entry.at(dir, ee), "") == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root,
        ""}}} : J.Res}
  {==}

def Laws.member_dep_named(
  name,
  ms,
  self,
  files,
  dir,
  nn,
  ee,
  bb,
  hh,
  pa,
  pv,
  ds,
  ts,
  hash,
  root,
  fs,
  sums,
  ef,
  eo,
  nv,
  en,
  ew
):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds,
      ts}}}, ef)
    : {J.target(_, self, name, files) == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}
  %Equal.sym(Bool, W.segs.eq(dir, self), False{}, eo)
    : {J.target.at(_, name, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}, dir, files, self) == J.Got{M.Dep{name,
        hash, J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByName{nv}, en)
    : {J.by.name(_, K.of(J.entry.at(dir, ee), files), name, J.entry.at(dir, ee)) == J.Got{M.Dep{name, hash,
        J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}
  %Equal.sym(K.Walked, K.of(J.entry.at(dir, ee), files), K.Walked{hash, root, fs, sums}, ew)
    : {J.walked(_, name, J.entry.at(dir, ee), nv) == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root,
        nv}}} : J.Res}
  {==}

def Laws.member_dep_unnamed(
  name,
  ms,
  self,
  files,
  dir,
  nn,
  ee,
  bb,
  hh,
  pa,
  pv,
  ds,
  ts,
  ef,
  eo,
  why,
  en
):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds,
      ts}}}, ef)
    : {J.target(_, self, name, files)
        == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}
  %Equal.sym(Bool, W.segs.eq(dir, self), False{}, eo)
    : {J.target.at(_, name, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}, dir, files, self)
        == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.Unnamed{why}, en)
    : {J.by.name(_, K.of(J.entry.at(dir, ee), files), name, J.entry.at(dir, ee))
        == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}
  {==}

def Laws.named_finds(dir, name, ee, bb, hh, pa, pv, ds, ts, ms):
  %Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
    : {J.named.at(_, J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}}, J.named(ms, name))
      == Some{J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}}} : Maybe<&2, J.Member>}
  {==}

def Laws.named_skips(hd, ms, name, en):
  %Equal.sym(Bool, String.eq(J.member.name(hd), name), False{}, en)
    : {J.named.at(_, hd, J.named(ms, name)) == J.named(ms, name) : Maybe<&2, J.Member>}
  {==}

def Laws.member_dep_unknown(name, ms, self, files, ef):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), None{}, ef)
    : {J.target(_, self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and no member's " ++
        "[package] is named " ++ name} : J.Res}
  {==}

def Laws.member_dep_own(name, ms, self, files, dir, mm, ef, eo):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, mm}}, ef)
    : {J.target(_, self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
      : J.Res}
  %Equal.sym(Bool, W.segs.eq(dir, self), True{}, eo)
    : {J.target.at(_, name, mm, dir, files, self)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
      : J.Res}
  {==}

def Laws.member_dep_hashed(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(hash), False{}, eg)
    : {J.section(Bool.and(Bool.and(_, String.is_empty(entry)), Bool.and(String.is_empty(path),
        String.is_empty(nv))), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_entried(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(entry), False{}, eg)
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), _), Bool.and(String.is_empty(path),
        String.is_empty(nv))), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(String.is_empty(hash), False{}), False{}, Str.and_false(String.is_empty(hash)))
    : {J.section(Bool.and(_, Bool.and(String.is_empty(path), String.is_empty(nv))), J.named(ms, name), self, name,
        files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_pathed(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(path), False{}, eg)
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), Bool.and(_,
        String.is_empty(nv))), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), False{}), False{},
      Str.and_false(Bool.and(String.is_empty(hash), String.is_empty(entry))))
    : {J.section(_, J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_nv(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(nv), False{}, eg)
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), Bool.and(String.is_empty(path),
        _)), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(String.is_empty(path), False{}), False{}, Str.and_false(String.is_empty(path)))
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), _), J.named(ms, name), self,
        name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), False{}), False{},
      Str.and_false(Bool.and(String.is_empty(hash), String.is_empty(entry))))
    : {J.section(_, J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_hub(_name, _hash, _entry, _nv, _ms, _self, _files):
  {==}

def Laws.member_dep_git(_name, _hash, _entry, _url, _rev, _tag, _root, _nar, _vend, _ms, _self, _files):
  {==}

def Laws.deps_res_refuses(dd, ds, ms, self, files, why, eb):
  %Equal.sym(J.Res, J.dep.res(dd, ms, self, files), J.Bad{why}, eb)
    : {J.deps.cons(_, J.deps.res(ds, ms, self, files)) == J.Unmet{why} : J.Deps}
  {==}

def Laws.res_one_refuses(dir, mm, ms, files, rest, why, eu):
  %Equal.sym(J.Deps, J.deps.res(J.deps.of(mm), ms, dir, files), J.Unmet{why}, eu)
    : {J.res.put(_, dir, mm, rest) == J.Unread{why} : J.Read}
  {==}

def Laws.res_one_keeps_refusal(dir, mm, ms, files, ds, why, eu):
  %Equal.sym(J.Deps, J.deps.res(J.deps.of(mm), ms, dir, files), J.Deps{ds}, eu)
    : {J.res.put(_, dir, mm, J.Unread{why}) == J.Unread{why} : J.Read}
  {==}

def Laws.resolve_refuses(root, ms, files, why, eu):
  %Equal.sym(J.Read, J.res.all(J.with.root(root, ms), J.with.root(root, ms), files), J.Unread{why}, eu)
    : {J.res.read(_, J.names.deps(J.with.root(root, ms), files)) == J.Clash{why} : J.Joint}
  {==}

def Laws.resolve_joins(root, ms, files, dir, rr, xs, ns, eu, en):
  %Equal.sym(J.Read, J.res.all(J.with.root(root, ms), J.with.root(root, ms), files),
    J.Read{J.Member{dir, rr} <> xs}, eu)
    : {J.res.read(_, J.names.deps(J.with.root(root, ms), files))
      == J.combine(J.with.deps(rr, List.append(&2, M.Dep, J.deps.of(rr), ns)), xs) : J.Joint}
  %Equal.sym(J.Deps, J.names.deps(J.with.root(root, ms), files), J.Deps{ns}, en)
    : {J.res.named(J.Member{dir, rr} <> xs, _)
      == J.combine(J.with.deps(rr, List.append(&2, M.Dep, J.deps.of(rr), ns)), xs) : J.Joint}
  {==}

def Laws.names_deps_named(dir, mm, xs, files, nv, dd, ds, en, eg, er):
  %Equal.sym(PP.Named, J.member.naming(J.Member{dir, mm}), PP.ByName{nv}, en)
    : {J.named.one(_, J.Member{dir, mm}, files, J.names.deps(xs, files)) == J.Deps{dd <> ds} : J.Deps}
  %Equal.sym(J.Res, J.member.dep(mm, dir, J.member.name(J.Member{dir, mm}), files), J.Got{dd}, eg)
    : {J.deps.cons(_, J.names.deps(xs, files)) == J.Deps{dd <> ds} : J.Deps}
  %Equal.sym(J.Deps, J.names.deps(xs, files), J.Deps{ds}, er)
    : {J.deps.cons(J.Got{dd}, _) == J.Deps{dd <> ds} : J.Deps}
  {==}

def Laws.names_deps_hashed(hd, xs, files, en):
  %Equal.sym(PP.Named, J.member.naming(hd), PP.ByHash{}, en)
    : {J.named.one(_, hd, files, J.names.deps(xs, files)) == J.names.deps(xs, files) : J.Deps}
  {==}

def Laws.member_name_recorded(_nn, hash, _entry, _path, nv, en):
  %Equal.sym(Bool, String.is_empty(nv), False{}, en)
    : {List.append(&2, L.Name, Bool.pick(List<&2, L.Name>, _, [], [L.Name{nv, hash}]), [])
      == [L.Name{nv, hash}] : List<&2, L.Name>}
  {==}

def Laws.seed_walked(_nn, hash, entry, path, _nv, files, hw, rw, fs, sums, ew):
  %Equal.sym(K.Walked, K.of(entry, files), K.Walked{hw, rw, fs, sums}, ew)
    : {J.seed.walked(_, hash, path, entry)
      == [LW.Reply{LW.Pkg{hash, L.Member{path, entry}, ""},
        LW.Got{LW.Clone{""}, K.manifest_of(sums), J.texts(sums, fs)}}] : List<&2, LW.Reply>}
  {==}

def Laws.seed_cloned(_hash, _src, _hub, _nar, _manifest, _ss):
  {==}

def Laws.member_origin(_nn, _hash, _entry, _path, _nv):
  {==}

def Laws.member_judged(_path, _entry, _nar, _hash, _manifest, _ss):
  {==}

def Laws.member_judged_lib(_path, _entry, _hash, _manifest, _ss):
  {==}

def Laws.member_src_reads(path, entry):
  LPF.src_read.member(path, entry)

def Laws.member_not_vended(_nn, _hash, _entry, _path, _nv, _ds):
  {==}

def Laws.member_laid(hash, vs, fs, ss, rest, ev):
  %Equal.sym(Bool, String.eq(hash, hash), True{}, Eq.string_eq_self(hash))
    : {LP.lay.pick(L.any.step(_, _u => L.seen.holds([], hash)), LW.Ok{fs, ss},
        LP.place.of(L.seen.holds(vs, hash)), hash, rest)
      == LP.lay.verdict(LW.Ok{fs, ss}, LP.Cache{}, hash, rest) : List<&2, LP.Effect>}
  %Equal.sym(Bool, L.seen.holds(vs, hash), False{}, ev)
    : {LP.lay.verdict(LW.Ok{fs, ss}, LP.place.of(_), hash, rest)
      == LP.lay.verdict(LW.Ok{fs, ss}, LP.Cache{}, hash, rest) : List<&2, LP.Effect>}
  {==}

def Laws.member_back_kept(_nn, _hash, _entry, _path, _nv, _joint):
  {==}

def Laws.member_not_missing(n, ps, ew):
  %Equal.sym(Bool, M.flag(M.value(ps, "workspace")), True{}, ew)
    : {Bool.and(String.starts_with(n, "deps."), Bool.and(Bool.not(_), String.is_empty(M.value(ps, "hash"))))
      == False{} : Bool}
  Str.and_false(String.starts_with(n, "deps."))

# ---------------------------------------------------------------------------
# a member imported by its hash, once it moved

def Laws.stale_plain_refuses(text, spec, fs, lock, world, why, ev, ew, en):
  %Equal.sym(Bool, LW.args.upgrade(world), False{}, ev)
    : {U.plan.at(_, U.Back{text, spec, fs, lock}, world) == LP.Plan{[], LP.Refused{why}} : LP.Plan}
  %Equal.sym(String, Mv.stale.world(lock, world), why, ew)
    : {U.plan.plain(String.is_empty(_), _, world) == LP.Plan{[], LP.Refused{why}} : LP.Plan}
  %Equal.sym(Bool, String.is_empty(why), False{}, en)
    : {U.plan.plain(_, why, world) == LP.Plan{[], LP.Refused{why}} : LP.Plan}
  {==}

def Laws.stale_plain_asks_nothing(text, spec, fs, lock, world, why, ev, ew, en):
  %Equal.sym(Bool, LW.args.upgrade(world), False{}, ev)
    : {U.step.plain(String.is_empty(U.stale.at(_, lock, world)), U.stale.at(_, lock, world),
        U.plans.on(U.Back{text, spec, fs, lock}, world))
      == LP.Run{LP.Plan{[], LP.Refused{why}}} : LP.Step}
  %Equal.sym(String, Mv.stale.world(lock, world), why, ew)
    : {U.step.plain(String.is_empty(_), _, U.plans.on(U.Back{text, spec, fs, lock}, world))
      == LP.Run{LP.Plan{[], LP.Refused{why}}} : LP.Step}
  %Equal.sym(Bool, String.is_empty(why), False{}, en)
    : {U.step.plain(_, why, U.plans.on(U.Back{text, spec, fs, lock}, world))
      == LP.Run{LP.Plan{[], LP.Refused{why}}} : LP.Step}
  {==}

def Laws.stale_names_upgrade(name, old, new, rest, at, text, eh):
  %Equal.sym(Bool, String.eq(LU.reimport.many([LU.Swap{old, new}], text), text), False{}, eh)
    : {Bool.pick(String, _, Mv.stale.moves(rest, at, text),
        "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
          ", the hash the lock records for it, and the member is " ++ new ++
          " now; ez lock --upgrade --package " ++ name ++ " rewrites the import")
      == "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
        ", the hash the lock records for it, and the member is " ++ new ++
        " now; ez lock --upgrade --package " ++ name ++ " rewrites the import" : String}
  {==}

def Laws.stale_skips_move(name, old, new, rest, at, text, eh):
  %Equal.sym(Bool, String.eq(LU.reimport.many([LU.Swap{old, new}], text), text), True{}, eh)
    : {Bool.pick(String, _, Mv.stale.moves(rest, at, text),
        "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
          ", the hash the lock records for it, and the member is " ++ new ++
          " now; ez lock --upgrade --package " ++ name ++ " rewrites the import")
      == Mv.stale.moves(rest, at, text) : String}
  {==}

def Laws.stale_first_file(ms, at, text, tl, why, eh, en):
  %Equal.sym(String, Mv.stale.moves(ms, at, text), why, eh)
    : {Bool.pick(String, String.is_empty(_), Mv.stale(ms, tl), _) == why : String}
  %Equal.sym(Bool, String.is_empty(why), False{}, en)
    : {Bool.pick(String, _, Mv.stale(ms, tl), why) == why : String}
  {==}

def Laws.stale_skips_file(ms, at, text, tl, eh):
  %Equal.sym(String, Mv.stale.moves(ms, at, text), "", eh)
    : {Bool.pick(String, String.is_empty(_), Mv.stale(ms, tl), _) == Mv.stale(ms, tl) : String}
  {==}

def Laws.move_chosen(_path, name, new, base, old, only, rest, eo, ec):
  %Equal.sym(Bool, String.eq(new, old), False{}, eo)
    : {Mv.move.put(Bool.and(Bool.not(_), Bool.or(LU.chosen(only, name), Bool.not(String.eq(new, base)))),
        name, old, new, rest) == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, LU.chosen(only, name), True{}, ec)
    : {Mv.move.put(Bool.or(_, Bool.not(String.eq(new, base))), name, old, new, rest)
      == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  {==}

def Laws.move_rewritten(_path, name, new, base, old, only, rest, eo, ec, eb):
  %Equal.sym(Bool, String.eq(new, old), False{}, eo)
    : {Mv.move.put(Bool.and(Bool.not(_), Bool.or(LU.chosen(only, name), Bool.not(String.eq(new, base)))),
        name, old, new, rest) == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, LU.chosen(only, name), False{}, ec)
    : {Mv.move.put(Bool.or(_, Bool.not(String.eq(new, base))), name, old, new, rest)
      == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, String.eq(new, base), False{}, eb)
    : {Mv.move.put(Bool.not(_), name, old, new, rest) == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  {==}

def Laws.move_same(_path, name, new, base, old, only, rest, eo):
  %Equal.sym(Bool, String.eq(new, old), True{}, eo)
    : {Mv.move.put(Bool.and(Bool.not(_), Bool.or(LU.chosen(only, name), Bool.not(String.eq(new, base)))),
        name, old, new, rest) == rest : List<&2, Mv.Shift>}
  {==}

def Laws.move_untouched(_path, name, new, base, old, only, rest, ec, eb):
  %Equal.sym(Bool, LU.chosen(only, name), False{}, ec)
    : {Mv.move.put(Bool.and(Bool.not(String.eq(new, old)), Bool.or(_, Bool.not(String.eq(new, base)))),
        name, old, new, rest) == rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, String.eq(new, base), True{}, eb)
    : {Mv.move.put(Bool.and(Bool.not(String.eq(new, old)), Bool.not(_)), name, old, new, rest) == rest
      : List<&2, Mv.Shift>}
  %Equal.sym(Bool, Bool.and(Bool.not(String.eq(new, old)), False{}), False{},
    Str.and_false(Bool.not(String.eq(new, old))))
    : {Mv.move.put(_, name, old, new, rest) == rest : List<&2, Mv.Shift>}
  {==}

def Laws.rewrite_reimports(_ss, _at, _text, _tl):
  {==}

def Laws.round_walks_again(_text, _fs, _files, _old, _base, _only, _ms):
  {==}

def Laws.cascade_stops(fuel, ctx, ms, es):
  %Equal.sym(Bool, Mv.moves.eq(ms, Mv.round(ctx, ms)), True{}, es)
    : {Mv.cascade.pick(_, ms, _u => Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms))) == ms : List<&2, Mv.Shift>}
  {==}

def Laws.cascade_goes_on(fuel, ctx, ms, es):
  %Equal.sym(Bool, Mv.moves.eq(ms, Mv.round(ctx, ms)), False{}, es)
    : {Mv.cascade.pick(_, ms, _u => Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms)))
      == Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms)) : List<&2, Mv.Shift>}
  {==}

def Laws.up_plans_moved(text, _spec, fs, lock, world, ev):
  %Equal.sym(Bool, LW.args.upgrade(world), True{}, ev)
    : {U.world.at(_, text, fs, lock, world)
      == Mv.world.moved(
        J.joint(text, fs, Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, U.files.of(world), lock,
          LW.args.only(world)))), U.files.of(world))),
        Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, U.files.of(world), lock, LW.args.only(world)))),
          U.files.of(world)),
        world) : LW.World}
  {==}

def Laws.edits_write_changed(ss, at, text, tl, ec, el):
  %Equal.sym(Bool, String.eq(LU.reimport.many(ss, text), text), False{}, ec)
    : {Mv.edit.put(Bool.not(_), at, LU.reimport.many(ss, text), Mv.edits(ss, tl))
      == LP.Write{at, LU.reimport.many(ss, text)} <> Mv.edits(ss, tl) : List<&2, LP.Effect>}
  %Equal.sym(Bool, String.eq(at, LP.lockfile()), False{}, el)
    : {Bool.pick(List<&2, LP.Effect>, _, Mv.edits(ss, tl), LP.Write{at, LU.reimport.many(ss, text)} <> Mv.edits(ss, tl))
      == LP.Write{at, LU.reimport.many(ss, text)} <> Mv.edits(ss, tl) : List<&2, LP.Effect>}
  {==}

def Laws.edits_skip_unchanged(ss, at, text, tl, ec):
  %Equal.sym(Bool, String.eq(LU.reimport.many(ss, text), text), True{}, ec)
    : {Mv.edit.put(Bool.not(_), at, LU.reimport.many(ss, text), Mv.edits(ss, tl)) == Mv.edits(ss, tl)
      : List<&2, LP.Effect>}
  {==}

# ---------------------------------------------------------------------------
# `ez doctor` over a workspace

def Laws.doc_alone(_world):
  {==}

def Laws.doc_judges_joint(_mm, _text, _fs):
  {==}

def Laws.doc_lines(_why, _text, _fs, _world):
  {==}

def Laws.doc_member_file(hd, tl, dirs, at, text, fs, eu):
  %Equal.sym(Bool, Doc.under(W.segs.text(hd <> tl), at), True{}, eu)
    : {Doc.own.put(_, LW.Source{at, text}, Doc.own.files(hd <> tl, dirs, fs))
      == LW.Source{at, text} <> Doc.own.files(hd <> tl, dirs, fs) : List<&2, LW.Source>}
  {==}

def Laws.doc_other_file(hd, tl, dirs, at, text, fs, eu):
  %Equal.sym(Bool, Doc.under(W.segs.text(hd <> tl), at), False{}, eu)
    : {Doc.own.put(_, LW.Source{at, text}, Doc.own.files(hd <> tl, dirs, fs))
      == Doc.own.files(hd <> tl, dirs, fs) : List<&2, LW.Source>}
  {==}

def Laws.doc_root_file(dirs, at, text, fs, eu):
  %Equal.sym(Bool, Doc.under.any(dirs, at), False{}, eu)
    : {Doc.own.put(Bool.not(_), LW.Source{at, text}, Doc.own.files([], dirs, fs))
      == LW.Source{at, text} <> Doc.own.files([], dirs, fs) : List<&2, LW.Source>}
  {==}

def Laws.doc_member_drift(_dir, _mm, _dirs, _nvs, _fs):
  {==}

def Laws.doc_drift_lines(_place, _hs, _ln, _ls):
  {==}

def Laws.doc_member_moved(_path, _name, held, root, now, en):
  %Equal.sym(Bool, String.eq(now, held), False{}, en)
    : {Bool.pick(List<&2, DP.Note>, _, [], [DP.Note{True{}, Doc.moved.line(root, now, held)}])
      == [DP.Note{True{}, Doc.moved.line(root, now, held)}] : List<&2, DP.Note>}
  {==}

def Laws.doc_member_same(_path, _name, held, root, now, en):
  %Equal.sym(Bool, String.eq(now, held), True{}, en)
    : {Bool.pick(List<&2, DP.Note>, _, [], [DP.Note{True{}, Doc.moved.line(root, now, held)}])
      == [] : List<&2, DP.Note>}
  {==}

def Laws.doc_member_walks(_dir, _nn, _ee, _bb, _hh, _pa, _pv, _ds, _ts, _files, _locked):
  {==}

def Laws.doc_fails_on_problem(why, text, fs, world, ew):
  %Equal.sym(Bool, DP.wrong(Doc.notes(why, text, fs, world)), True{}, ew)
    : {DP.refuses.plan(LP.Plan{DP.says(Doc.notes(why, text, fs, world)), DP.outcome.of(_)}) == True{} : Bool}
  {==}

def Laws.doc_passes_when_fine(why, text, fs, world, ew):
  %Equal.sym(Bool, DP.wrong(Doc.notes(why, text, fs, world)), False{}, ew)
    : {DP.refuses.plan(LP.Plan{DP.says(Doc.notes(why, text, fs, world)), DP.outcome.of(_)}) == False{} : Bool}
  {==}

def Laws.doc_writes_nothing(back, world):
  match back:
    case Doc.Alone{}:
      DL.doctor_writes_nothing(world)
    case Doc.Back{+text, +fs, +why}:
      DPF.says_quiet(Doc.notes(why, text, fs, world))
