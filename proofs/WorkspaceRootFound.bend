# proofs of laws/WorkspaceRootFound.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/root.bend as RRoot
import ../laws/WorkspaceRootFound.bend as Laws
import ../laws/defs/DirectorySplits.bend as D1
import ../laws/defs/LockInputs.bend as D2

# ---------------------------------------------------------------------------
# finding the root

# by induction on where ez runs: the directories above the parent, one
# segment further down, start with the parent
def Laws.asks_nearest(here):
  match here:
    case []:
      {==}
    case +hd <> +tl:
      Equal.cong(List<&2, RRoot.Ask>, List<&2, RRoot.Ask>,
        xs => List.append(&2, RRoot.Ask, RRoot.asks.under(hd, xs), [RRoot.Ask{[], hd <> tl}]),
        RRoot.asks(tl), RRoot.Ask{tl, []} <> Laws.asks.rest(tl), Laws.asks_nearest(tl))

# the top is put last, at the top and with a segment in front alike
def Laws.asks_top(here):
  match here:
    case []:
      {==}
    case _hd <> _tl:
      {==}

# a path compares equal to itself, segment by segment
def segs_eq_self(ds: List<&2, String>) -> {WWorkspace.segs.eq(ds, ds) == True{} : Bool}:
  match ds:
    case []:
      {==}
    case +hd <> +tl:
      Str.and_true(String.eq(hd, hd), WWorkspace.segs.eq(tl, tl), Eq.string_eq_self(hd), segs_eq_self(tl))

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
  xs: List<&2, RRoot.Ask>,
  +ys: List<&2, RRoot.Ask>,
  +here: List<&2, String>
) -> {D1.splits(List.append(&2, RRoot.Ask, xs, ys), here)
    == Bool.and(D1.splits(xs, here), D1.splits(ys, here)) : Bool}:
  match xs:
    case []:
      {==}
    case RRoot.Ask{+ds, +rs} <> +xt:
      Equal.trans(Bool,
        Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), here),
          D1.splits(List.append(&2, RRoot.Ask, xt, ys), here)),
        Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), here),
          Bool.and(D1.splits(xt, here), D1.splits(ys, here))),
        Bool.and(Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), here), D1.splits(xt, here)),
          D1.splits(ys, here)),
        Equal.cong(Bool, Bool, bb => Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), here), bb),
          D1.splits(List.append(&2, RRoot.Ask, xt, ys), here),
          Bool.and(D1.splits(xt, here), D1.splits(ys, here)),
          splits_app(xt, ys, here)),
        and_assoc(WWorkspace.segs.eq(List.append(&2, String, ds, rs), here), D1.splits(xt, here),
          D1.splits(ys, here)))

# directories asked about from one segment further down split where ez runs
# when they split one segment further down
def splits_under(
  +hd: String,
  xs: List<&2, RRoot.Ask>,
  +tl: List<&2, String>
) -> {D1.splits(RRoot.asks.under(hd, xs), hd <> tl) == D1.splits(xs, tl) : Bool}:
  match xs:
    case []:
      {==}
    case RRoot.Ask{+ds, +rs} <> +xt:
      Equal.trans(Bool,
        Bool.and(Bool.and(String.eq(hd, hd), WWorkspace.segs.eq(List.append(&2, String, ds, rs), tl)),
          D1.splits(RRoot.asks.under(hd, xt), hd <> tl)),
        Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), tl),
          D1.splits(RRoot.asks.under(hd, xt), hd <> tl)),
        Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), tl), D1.splits(xt, tl)),
        Equal.cong(Bool, Bool,
          bb => Bool.and(Bool.and(bb, WWorkspace.segs.eq(List.append(&2, String, ds, rs), tl)),
            D1.splits(RRoot.asks.under(hd, xt), hd <> tl)),
          String.eq(hd, hd), True{}, Eq.string_eq_self(hd)),
        Equal.cong(Bool, Bool, bb => Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), tl), bb),
          D1.splits(RRoot.asks.under(hd, xt), hd <> tl), D1.splits(xt, tl),
          splits_under(hd, xt, tl)))

# by induction on where ez runs: the directories above the parent split
# there, one segment further down, and the top is the whole path above it
def Laws.asks_split(here):
  match here:
    case []:
      {==}
    case +hd <> +tl:
      Equal.trans(Bool,
        D1.splits(List.append(&2, RRoot.Ask, RRoot.asks.under(hd, RRoot.asks(tl)), [RRoot.Ask{[], hd <> tl}]),
            hd <> tl),
        Bool.and(D1.splits(RRoot.asks.under(hd, RRoot.asks(tl)), hd <> tl),
          D1.splits([RRoot.Ask{[], hd <> tl}], hd <> tl)),
        True{},
        splits_app(RRoot.asks.under(hd, RRoot.asks(tl)), [RRoot.Ask{[], hd <> tl}], hd <> tl),
        Str.and_true(D1.splits(RRoot.asks.under(hd, RRoot.asks(tl)), hd <> tl),
          D1.splits([RRoot.Ask{[], hd <> tl}], hd <> tl),
          Equal.trans(Bool, D1.splits(RRoot.asks.under(hd, RRoot.asks(tl)), hd <> tl),
            D1.splits(RRoot.asks(tl), tl), True{},
            splits_under(hd, RRoot.asks(tl), tl), Laws.asks_split(tl)),
          Str.and_true(WWorkspace.segs.eq(hd <> tl, hd <> tl), True{}, segs_eq_self(hd <> tl), {==})))

def Laws.root_skips_none(_ds, _rs, _ups):
  {==}

def Laws.root_skips_lone(ds, rs, tt, ups, ev):
  Equal.cong(WWorkspace.Read, RRoot.Found, rd => RRoot.root.read(rd, ds, rs, RRoot.root.go(ups)),
      WWorkspace.spec.of(tt), WWorkspace.Lone{}, ev)

def Laws.root_bad_refuses(ds, rs, tt, ups, why, ev):
  Equal.cong(WWorkspace.Read, RRoot.Found, rd => RRoot.root.read(rd, ds, rs, RRoot.root.go(ups)),
      WWorkspace.spec.of(tt), WWorkspace.Bad{why}, ev)

def Laws.root_claims_it(ds, rs, tt, ups, spec, ev, ec):
  Equal.trans(RRoot.Found,
    RRoot.root.read(WWorkspace.spec.of(tt), ds, rs, RRoot.root.go(ups)),
    RRoot.root.claim(RRoot.claims(spec, rs), ds, rs, RRoot.root.go(ups)),
    RRoot.Within{ds, rs},
    Equal.cong(WWorkspace.Read, RRoot.Found, rd => RRoot.root.read(rd, ds, rs, RRoot.root.go(ups)),
        WWorkspace.spec.of(tt), WWorkspace.Root{spec}, ev),
    Equal.cong(Bool, RRoot.Found, bb => RRoot.root.claim(bb, ds, rs, RRoot.root.go(ups)), RRoot.claims(spec, rs),
        True{}, ec))

def Laws.root_passes_by(ds, rs, tt, ups, spec, ev, ec):
  Equal.trans(RRoot.Found,
    RRoot.root.read(WWorkspace.spec.of(tt), ds, rs, RRoot.root.go(ups)),
    RRoot.root.claim(RRoot.claims(spec, rs), ds, rs, RRoot.root.go(ups)),
    RRoot.root.go(ups),
    Equal.cong(WWorkspace.Read, RRoot.Found, rd => RRoot.root.read(rd, ds, rs, RRoot.root.go(ups)),
        WWorkspace.spec.of(tt), WWorkspace.Root{spec}, ev),
    Equal.cong(Bool, RRoot.Found, bb => RRoot.root.claim(bb, ds, rs, RRoot.root.go(ups)), RRoot.claims(spec, rs),
        False{}, ec))

# a ledger that says nothing of a workspace leaves the search to the
# directories above
def quiet_read(
  rd: WWorkspace.Read,
  +ds: List<&2, String>,
  +rs: List<&2, String>,
  rest: RRoot.Found,
  ev: {D2.quiet.read(rd) == True{} : Bool}
) -> {RRoot.root.read(rd, ds, rs, rest) == rest : RRoot.Found}:
  match rd:
    case WWorkspace.Lone{}:
      {==}
    case WWorkspace.Bad{why}:
      Eq.bit.absurd(&2, {RRoot.root.read(WWorkspace.Bad{why}, ds, rs, rest) == rest : RRoot.Found}, ev)
    case WWorkspace.Root{spec}:
      Eq.bit.absurd(&2, {RRoot.root.read(WWorkspace.Root{spec}, ds, rs, rest) == rest : RRoot.Found}, ev)

# and so does a directory with no ledger
def quiet_at(
  text: Maybe<&2, String>,
  +ds: List<&2, String>,
  +rs: List<&2, String>,
  rest: RRoot.Found,
  ev: {D2.quiet.one(text) == True{} : Bool}
) -> {RRoot.root.at(text, ds, rs, rest) == rest : RRoot.Found}:
  match text:
    case None{}:
      {==}
    case Some{tt}:
      quiet_read(WWorkspace.spec.of(tt), ds, rs, rest, ev)

# by induction on the directories read: each leaves the search to the rest
def Laws.root_none(ups, ev):
  match ups:
    case []:
      {==}
    case RRoot.Up{+ds, +rs, +tx} <> +tl:
      Equal.trans(RRoot.Found, RRoot.root.at(tx, ds, rs, RRoot.root.go(tl)), RRoot.root.go(tl), RRoot.Alone{},
        quiet_at(tx, ds, rs, RRoot.root.go(tl), Eq.and.left(D2.quiet.one(tx), D2.quiet(tl), ev)),
        Laws.root_none(tl, Eq.and.right(D2.quiet.one(tx), D2.quiet(tl), ev)))

def Laws.claims_self(_spec):
  {==}

def Laws.claims_member(_spec, _hd, _tl):
  {==}

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
