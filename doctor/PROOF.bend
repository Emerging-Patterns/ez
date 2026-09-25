# doctor: the proofs. `bend PROOF.bend` is the gate.
#
# The plan is `plan.notes` of every line doctor found: each line said, and
# the command failed when one is a problem. Every effect is a `Say`, so the
# law that doctor writes nothing is an induction over the lines. The drift
# report is the last part of the lines, after the toolchain, the ledger, the
# lock and the library, so a law about what doctor says of the drift is a
# law about that last part, carried through the ones before it by `said_append`;
# a law that doctor fails is `wrong_append` the same way. The report itself is
# list membership: a hash the source imports and the ledger lacks survives
# `missing`, and its line is in `unrecorded`; a dependency no import names
# keeps its line in `unused`. Membership is `DP.has`, whose step is decided
# by `String.eq`, so each lemma splits on that answer, and an answer of True
# is turned into equal strings by `string_eq_true`.
import Base
import ./world.bend as DW
import ./plan.bend as DP
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/lock.bend as L
import ../ledger/manifest.bend as M
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ./LAWS.bend as Laws

# ---------------------------------------------------------------------------
# a step of a scan

# LAW: a step whose rest answers True answers True, whatever its head said
law step_true:
  for b: Bool
  for r: Unit -> Bool
  for e: {r(Unit{}) == True{} : Bool}
  {DP.has.step(b, r) == True{} : Bool}

def step_true(b, _r, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

# LAW: and so does a step whose head answered True
law step_hit:
  for b: Bool
  for r: Unit -> Bool
  for e: {b == True{} : Bool}
  {DP.has.step(b, r) == True{} : Bool}

def step_hit(b, r, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {DP.has.step(False{}, r) == True{} : Bool}, e)

# ---------------------------------------------------------------------------
# the plan writes nothing

# LAW: the lines of a report, said, write nothing
law says_quiet:
  for ns: List<&2, DP.Note>
  {P.writes.in(DP.says(ns)) == False{} : Bool}

def says_quiet(ns):
  match ns:
    case []:
      {==}
    case h <> t:
      match h:
        case DP.Note{_w, _l}:
          says_quiet(t)

def Laws.doctor_writes_nothing(w):
  says_quiet(DP.notes.of(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}),
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w)))

# ---------------------------------------------------------------------------
# what a plan says

# LAW: a line said by the rest of the lines is said by all of them
law said_cons:
  for n: DP.Note
  for +rest: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(rest), line) == True{} : Bool}
  {DP.said.in(DP.says(n <> rest), line) == True{} : Bool}

def said_cons(n, rest, line, e):
  match n:
    case DP.Note{_w, l}:
      step_true(String.eq(l, line), _u => DP.said.in(DP.says(rest), line), e)

# LAW: and a line said by the last lines is said by all of them
law said_append:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(b), line) == True{} : Bool}
  {DP.said.in(DP.says(List.append(&2, DP.Note, a, b)), line) == True{} : Bool}

def said_append(a, b, line, e):
  match a:
    case []:
      e
    case h <> +t:
      said_cons(h, List.append(&2, DP.Note, t, b), line, said_append(t, b, line, e))

# LAW: one line of a flagged report, with its head decided
law said_flag.step:
  for b: Bool
  for +t: List<&2, String>
  for +line: String
  for e: {DP.has.step(b, _u => DP.has(t, line)) == True{} : Bool}
  for ih: {DP.has(t, line) == True{} : Bool}
    -> {DP.said.in(DP.says(DP.flag(t)), line) == True{} : Bool}
  {DP.has.step(b, _u => DP.said.in(DP.says(DP.flag(t)), line)) == True{} : Bool}

def said_flag.step(b, _t, _line, e, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: every line of a report is said once the report is flagged
law said_flag:
  for ls: List<&2, String>
  for +line: String
  for e: {DP.has(ls, line) == True{} : Bool}
  {DP.said.in(DP.says(DP.flag(ls)), line) == True{} : Bool}

def said_flag(ls, line, e):
  match ls:
    case []:
      Eq.bit.absurd(&2, {DP.said.in(DP.says(DP.flag([])), line) == True{} : Bool}, e)
    case +l <> +t:
      said_flag.step(String.eq(l, line), t, line, e, x => said_flag(t, line, x))

# LAW: and every line of a drift report is said
law said_drift:
  for +hs: List<&2, String>
  for ls: List<&2, String>
  for +line: String
  for e: {DP.has(ls, line) == True{} : Bool}
  {DP.said.in(DP.says(DP.drift.notes(hs, ls)), line) == True{} : Bool}

def said_drift(hs, ls, line, e):
  match ls:
    case []:
      Eq.bit.absurd(&2, {DP.said.in(DP.says(DP.drift.notes(hs, [])), line) == True{} : Bool}, e)
    case +l <> +t:
      said_flag(l <> t, line, e)

# LAW: a line the drift report says is said by doctor, after everything else
law said_notes:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(DP.imports.notes(led, got)), line) == True{} : Bool}
  {DP.said.in(DP.says(DP.notes.of(led, got, cc, lib, lock, rs, cs)), line) == True{} : Bool}

def said_notes(led, got, cc, lib, lock, rs, cs, line, e):
  said_append(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got), line, e)

# ---------------------------------------------------------------------------
# membership

# LAW: a list holds what its tail holds, with anything before it
law has_append_right:
  for a: List<&2, String>
  for +b: List<&2, String>
  for +x: String
  for e: {DP.has(b, x) == True{} : Bool}
  {DP.has(List.append(&2, String, a, b), x) == True{} : Bool}

def has_append_right(a, b, x, e):
  match a:
    case []:
      e
    case +y <> +t:
      step_true(String.eq(y, x), _u => DP.has(List.append(&2, String, t, b), x),
        has_append_right(t, b, x, e))

# LAW: one step of the front, with its head decided
law has_append_left.step:
  for bb: Bool
  for +t: List<&2, String>
  for +b: List<&2, String>
  for +x: String
  for e: {DP.has.step(bb, _u => DP.has(t, x)) == True{} : Bool}
  for ih: {DP.has(t, x) == True{} : Bool}
    -> {DP.has(List.append(&2, String, t, b), x) == True{} : Bool}
  {DP.has.step(bb, _u => DP.has(List.append(&2, String, t, b), x)) == True{} : Bool}

def has_append_left.step(bb, _t, _b, _x, e, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: and what its front holds, with anything after it
law has_append_left:
  for a: List<&2, String>
  for +b: List<&2, String>
  for +x: String
  for e: {DP.has(a, x) == True{} : Bool}
  {DP.has(List.append(&2, String, a, b), x) == True{} : Bool}

def has_append_left(a, b, x, e):
  match a:
    case []:
      Eq.bit.absurd(&2, {DP.has(List.append(&2, String, [], b), x) == True{} : Bool}, e)
    case +y <> +t:
      has_append_left.step(String.eq(y, x), t, b, x, e, z => has_append_left(t, b, x, z))

# LAW: a list that holds one string holds any string equal to it
law has_at:
  for +ss: List<&2, String>
  for x: String
  for h: String
  for xh: {x == h : String}
  for e: {DP.has(ss, x) == True{} : Bool}
  {DP.has(ss, h) == True{} : Bool}

def has_at(ss, _x, _h, xh, e):
  %xh : {DP.has(ss, _) == True{} : Bool}
  e

# LAW: a head kept by `once`, with what it equals decided
law once_keep:
  for bb: Bool
  for +t: List<&2, String>
  for +h: String
  for ih: {DP.has(DP.once(t), h) == DP.has(t, h) : Bool}
  {DP.has.step(bb, _u => DP.has(DP.once(t), h)) == DP.has.step(bb, _u => DP.has(t, h))
    : Bool}

def once_keep(bb, _t, _h, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: a head `once` drops, because the rest holds it again
law once_dup:
  for bb: Bool
  for +x: String
  for +t: List<&2, String>
  for +h: String
  for eb: {String.eq(x, h) == bb : Bool}
  for ec: {DP.has(t, x) == True{} : Bool}
  for ih: {DP.has(DP.once(t), h) == DP.has(t, h) : Bool}
  {DP.has(DP.once(t), h) == DP.has.step(bb, _u => DP.has(t, h)) : Bool}

def once_dup(bb, x, t, h, eb, ec, ih):
  match bb:
    case True{}:
      Equal.trans(Bool, DP.has(DP.once(t), h), DP.has(t, h), True{}, ih,
        has_at(t, x, h, Str.string_eq_true(x, h, eb), ec))
    case False{}:
      ih

# LAW: one step of `once`, with whether the rest holds the head decided
law once_split:
  for c: Bool
  for +x: String
  for +t: List<&2, String>
  for +h: String
  for ec: {DP.has(t, x) == c : Bool}
  for ih: {DP.has(DP.once(t), h) == DP.has(t, h) : Bool}
  {DP.has(DP.once.put(c, x, DP.once(t)), h) == DP.has(x <> t, h) : Bool}

def once_split(c, x, t, h, ec, ih):
  match c:
    case True{}:
      once_dup(String.eq(x, h), x, t, h, {==}, ec, ih)
    case False{}:
      once_keep(String.eq(x, h), t, h, ih)

# LAW: `once` holds exactly what its list holds
law once_has:
  for xs: List<&2, String>
  for +h: String
  {DP.has(DP.once(xs), h) == DP.has(xs, h) : Bool}

def once_has(xs, h):
  match xs:
    case []:
      {==}
    case +x <> +t:
      once_split(DP.has(t, x), x, t, h, {==}, once_has(t, h))

# LAW: one step of `missing`, with both of its answers decided
law missing_hit:
  for b: Bool
  for c: Bool
  for +x: String
  for +t: List<&2, String>
  for +known: List<&2, String>
  for +h: String
  for eb: {String.eq(x, h) == b : Bool}
  for ec: {DP.has(known, x) == c : Bool}
  for e1: {DP.has.step(b, _u => DP.has(t, h)) == True{} : Bool}
  for e2: {False{} == DP.has(known, h) : Bool}
  for ih: {DP.has(t, h) == True{} : Bool}
    -> {DP.has(DP.missing(t, known), h) == True{} : Bool}
  {DP.has(DP.missing.put(c, x, DP.missing(t, known)), h) == True{} : Bool}

def missing_hit(b, c, x, t, known, h, eb, ec, e1, e2, ih):
  match b:
    case True{}:
      match c:
        case True{}:
          Eq.bit.absurd(&2,
            {DP.has(DP.missing.put(True{}, x, DP.missing(t, known)), h) == True{} : Bool},
            Equal.trans(Bool, False{}, DP.has(known, h), True{}, e2,
              has_at(known, x, h, Str.string_eq_true(x, h, eb), ec)))
        case False{}:
          step_hit(String.eq(x, h), _u => DP.has(DP.missing(t, known), h), eb)
    case False{}:
      match c:
        case True{}:
          ih(e1)
        case False{}:
          step_true(String.eq(x, h), _u => DP.has(DP.missing(t, known), h), ih(e1))

# LAW: a string a list holds and `known` does not is one `missing` keeps
law missing_has:
  for xs: List<&2, String>
  for +known: List<&2, String>
  for +h: String
  for e1: {DP.has(xs, h) == True{} : Bool}
  for +e2: {False{} == DP.has(known, h) : Bool}
  {DP.has(DP.missing(xs, known), h) == True{} : Bool}

def missing_has(xs, known, h, e1, e2):
  match xs:
    case []:
      Eq.bit.absurd(&2, {DP.has(DP.missing([], known), h) == True{} : Bool}, e1)
    case +x <> +t:
      missing_hit(String.eq(x, h), DP.has(known, x), x, t, known, h, {==}, {==}, e1, e2,
        z => missing_has(t, known, h, z, e2))

# LAW: equal hashes make equal report lines
law line_eq:
  for +x: String
  for h: String
  for xh: {x == h : String}
  {String.eq(DP.unrecorded.line(x), DP.unrecorded.line(h)) == True{} : Bool}

def line_eq(x, _h, xh):
  %xh : {String.eq(DP.unrecorded.line(x), DP.unrecorded.line(_)) == True{} : Bool}
  Eq.string_eq_self(DP.unrecorded.line(x))

# LAW: one step of the unrecorded lines, with its head decided
law unrecorded_hit:
  for b: Bool
  for +x: String
  for +t: List<&2, String>
  for +h: String
  for eb: {String.eq(x, h) == b : Bool}
  for e: {DP.has.step(b, _u => DP.has(t, h)) == True{} : Bool}
  for ih: {DP.has(t, h) == True{} : Bool}
    -> {DP.has(DP.unrecorded(t), DP.unrecorded.line(h)) == True{} : Bool}
  {DP.has.step(String.eq(DP.unrecorded.line(x), DP.unrecorded.line(h)),
    _u => DP.has(DP.unrecorded(t), DP.unrecorded.line(h))) == True{} : Bool}

def unrecorded_hit(b, x, t, h, eb, e, ih):
  match b:
    case True{}:
      step_hit(String.eq(DP.unrecorded.line(x), DP.unrecorded.line(h)),
        _u => DP.has(DP.unrecorded(t), DP.unrecorded.line(h)),
        line_eq(x, h, Str.string_eq_true(x, h, eb)))
    case False{}:
      step_true(String.eq(DP.unrecorded.line(x), DP.unrecorded.line(h)),
        _u => DP.has(DP.unrecorded(t), DP.unrecorded.line(h)), ih(e))

# LAW: every hash of a list has its line among the unrecorded lines
law unrecorded_has:
  for xs: List<&2, String>
  for +h: String
  for e: {DP.has(xs, h) == True{} : Bool}
  {DP.has(DP.unrecorded(xs), DP.unrecorded.line(h)) == True{} : Bool}

def unrecorded_has(xs, h, e):
  match xs:
    case []:
      Eq.bit.absurd(&2, {DP.has(DP.unrecorded([]), DP.unrecorded.line(h)) == True{} : Bool}, e)
    case +x <> +t:
      unrecorded_hit(String.eq(x, h), x, t, h, {==}, e, z => unrecorded_has(t, h, z))

# LAW: a line among the rest stays whatever the head's fate
law unused_put:
  for c: Bool
  for +x: M.Dep
  for +rest: List<&2, String>
  for +target: String
  for ih: {DP.has(rest, target) == True{} : Bool}
  {DP.has(DP.unused.put(c, x, rest), target) == True{} : Bool}

def unused_put(c, x, rest, target, ih):
  match c:
    case True{}:
      ih
    case False{}:
      step_true(String.eq(DP.unused.line(x), target), _u => DP.has(rest, target), ih)

# LAW: a dependency no import names has its line among the unused lines,
# wherever it stands
law unused_has:
  for pre: List<&2, M.Dep>
  for +d: M.Dep
  for +post: List<&2, M.Dep>
  for +hs: List<&2, String>
  for +e: {False{} == DP.used(hs, d) : Bool}
  {DP.has(DP.unused(List.append(&2, M.Dep, pre, d <> post), hs), DP.unused.line(d)) == True{}
    : Bool}

def unused_has(pre, d, post, hs, e):
  match pre:
    case []:
      %e : {DP.has(DP.unused.put(_, d, DP.unused(post, hs)), DP.unused.line(d)) == True{}
        : Bool}
      step_hit(String.eq(DP.unused.line(d), DP.unused.line(d)),
        _u => DP.has(DP.unused(post, hs), DP.unused.line(d)),
        Eq.string_eq_self(DP.unused.line(d)))
    case +x <> +t:
      unused_put(DP.used(hs, x), x,
        DP.unused(List.append(&2, M.Dep, t, d <> post), hs), DP.unused.line(d),
        unused_has(t, d, post, hs, e))

# ---------------------------------------------------------------------------
# EZ-VEN-5

def Laws.doctor_reports_unrecorded(w, n, e, b, hub, hubpa, hubpv, ds, _ts, fs, h, g, l, i, u):
  %g : {DP.said(DP.plan.of(DP.ledger.seen(_), DW.cc(w), DW.lib(w), DW.lock(w),
    DW.replies(w), DP.checked(w)), DP.unrecorded.line(h)) == True{} : Bool}
  %l : {DP.said.in(DP.says(DP.notes.of(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, _,
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w))), DP.unrecorded.line(h))
    == True{} : Bool}
  said_notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, DW.Heard{DW.Listed{W.Listed{fs}}},
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), DP.unrecorded.line(h),
    said_drift(DP.imports(fs), DP.drift(DP.imports(fs), ds), DP.unrecorded.line(h),
      has_append_left(DP.unrecorded(DP.missing(DP.imports(fs), DP.pinned(ds))),
        DP.unused(ds, DP.imports(fs)), DP.unrecorded.line(h),
        unrecorded_has(DP.missing(DP.imports(fs), DP.pinned(ds)), h,
          missing_has(DP.imports(fs), DP.pinned(ds), h,
            Equal.trans(Bool, DP.has(DP.imports(fs), h),
              DP.has(List.append(&2, String, P.roots(fs), P.roots.named(fs)), h), True{},
              once_has(List.append(&2, String, P.roots(fs), P.roots.named(fs)), h),
              has_append_left(P.roots(fs), P.roots.named(fs), h, i)),
            u)))))

def Laws.doctor_reports_unused(w, n, e, b, hub, hubpa, hubpv, pre, d, post, _ts, fs, g, l, u):
  %g : {DP.said(DP.plan.of(DP.ledger.seen(_), DW.cc(w), DW.lib(w), DW.lock(w),
    DW.replies(w), DP.checked(w)), DP.unused.line(d)) == True{} : Bool}
  %l : {DP.said.in(DP.says(DP.notes.of(
    M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, List.append(&2, M.Dep, pre, d <> post), []}}, _,
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w))), DP.unused.line(d))
    == True{} : Bool}
  said_notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, List.append(&2, M.Dep, pre, d <> post), []}},
    DW.Heard{DW.Listed{W.Listed{fs}}},
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), DP.unused.line(d),
    said_drift(DP.imports(fs),
      DP.drift(DP.imports(fs), List.append(&2, M.Dep, pre, d <> post)), DP.unused.line(d),
      has_append_right(
        DP.unrecorded(DP.missing(DP.imports(fs),
          DP.pinned(List.append(&2, M.Dep, pre, d <> post)))),
        DP.unused(List.append(&2, M.Dep, pre, d <> post), DP.imports(fs)),
        DP.unused.line(d),
        unused_has(pre, d, post, DP.imports(fs), u))))

# LAW: a report with a problem in its last part has a problem
law wrong_append:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for e: {DP.wrong(b) == True{} : Bool}
  {DP.wrong(List.append(&2, DP.Note, a, b)) == True{} : Bool}

def wrong_append(a, b, e):
  match a:
    case []:
      e
    case +h <> +t:
      step_true(DP.note.wrong(h), _u => DP.wrong(List.append(&2, DP.Note, t, b)),
        wrong_append(t, b, e))

# LAW: one step of the front, with its head decided
law wrong_left.step:
  for bb: Bool
  for +t: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for e: {DP.has.step(bb, _u => DP.wrong(t)) == True{} : Bool}
  for ih: {DP.wrong(t) == True{} : Bool}
    -> {DP.wrong(List.append(&2, DP.Note, t, b)) == True{} : Bool}
  {DP.has.step(bb, _u => DP.wrong(List.append(&2, DP.Note, t, b))) == True{} : Bool}

def wrong_left.step(bb, _t, _b, e, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: and one with a problem in its front has one
law wrong_append_left:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for e: {DP.wrong(a) == True{} : Bool}
  {DP.wrong(List.append(&2, DP.Note, a, b)) == True{} : Bool}

def wrong_append_left(a, b, e):
  match a:
    case []:
      Eq.bit.absurd(&2, {DP.wrong(List.append(&2, DP.Note, [], b)) == True{} : Bool}, e)
    case h <> +t:
      wrong_left.step(DP.note.wrong(h), t, b, e, z => wrong_append_left(t, b, z))

# LAW: a plan over lines with a problem fails the command
law refuses_wrong:
  for +ns: List<&2, DP.Note>
  for e: {DP.wrong(ns) == True{} : Bool}
  {DP.refuses.plan(DP.plan.notes(ns)) == True{} : Bool}

def refuses_wrong(ns, e):
  %Equal.sym(Bool, DP.wrong(ns), True{}, e)
    : {DP.refuses.plan(P.Plan{DP.says(ns), DP.outcome.of(_)}) == True{} : Bool}
  {==}

def Laws.doctor_drift_fails(w, n, e, b, hub, hubpa, hubpv, ds, _ts, fs, x, xs, g, l, r):
  %g : {DP.refuses.plan(DP.plan.of(DP.ledger.seen(_), DW.cc(w), DW.lib(w), DW.lock(w),
    DW.replies(w), DP.checked(w))) == True{} : Bool}
  %l : {DP.refuses.plan(DP.plan.notes(DP.notes.of(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}},
    _, DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w)))) == True{} : Bool}
  %Equal.sym(List<&2, String>, DP.drift.of(fs, ds), x <> xs, r)
    : {DP.refuses.plan(DP.plan.notes(List.append(&2, DP.Note,
      DP.head.notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, DW.cc(w), DW.lib(w), DW.lock(w),
        DW.replies(w), DP.checked(w)),
      DP.drift.notes(DP.imports(fs), _)))) == True{} : Bool}
  refuses_wrong(List.append(&2, DP.Note,
      DP.head.notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, DW.cc(w), DW.lib(w), DW.lock(w),
        DW.replies(w), DP.checked(w)),
      DP.flag(x <> xs)),
    wrong_append(DP.head.notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, DW.cc(w), DW.lib(w),
      DW.lock(w), DW.replies(w), DP.checked(w)), DP.flag(x <> xs), {==}))

# ---------------------------------------------------------------------------
# a ledger that is not there, or not read

# LAW: doctor fails on a ledger it could not read, whatever else it found
law bad_fails:
  for +why: String
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  {DP.refuses.plan(DP.plan.of(M.Bad{why}, cc, lib, lock, rs, cs)) == True{} : Bool}

def bad_fails(why, cc, lib, lock, rs, cs):
  refuses_wrong(DP.notes.of(M.Bad{why}, DW.heard(rs, DW.Sources{}), cc, lib, lock, rs, cs),
    wrong_append_left(DP.head.notes(M.Bad{why}, cc, lib, lock, rs, cs),
      DP.imports.notes(M.Bad{why}, DW.heard(rs, DW.Sources{})),
      wrong_append(DP.probes(DP.programs(cc), rs),
        List.append(&2, DP.Note,
          [DP.ledger.note(M.Bad{why}), DP.lock.note(0n, DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
        wrong_append_left(
          [DP.ledger.note(M.Bad{why}), DP.lock.note(0n, DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
          {==}))))

def Laws.doctor_needs_ledger(cc, lib, lock, rs):
  bad_fails("none here; ez init makes one", cc, lib, lock, rs,
    DP.checked(DW.World{cc, lib, None{}, lock, rs}))

def Laws.doctor_refuses_unread(cc, lib, lock, rs, s, why, bad):
  %bad : {DP.refuses.plan(DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs,
    DP.checked(DW.World{cc, lib, Some{s}, lock, rs}))) == True{} : Bool}
  bad_fails(why, cc, lib, lock, rs, DP.checked(DW.World{cc, lib, Some{s}, lock, rs}))

# ---------------------------------------------------------------------------
# EZ-LED-5

# Both ledgers are seen without their tools, which is the same ledger.
def Laws.doctor_ignores_tools(cc, lib, lock, rs, cs, _t1, t2, n, e, b, hub, hubpa, hubpv, ds, ts1, _ts2, g1, g2):
  %g1 : {DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs, cs)
    == DP.plan.of(DP.ledger.seen(M.parse(t2)), cc, lib, lock, rs, cs) : P.Plan}
  %g2 : {DP.plan.of(DP.ledger.seen(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, ts1}}), cc, lib, lock,
    rs, cs) == DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs, cs) : P.Plan}
  {==}

# ---------------------------------------------------------------------------
# the lock's verdict turns on the list first, so the no-dependency law splits
# on it and the other two are the arm they name

def Laws.lock_needless(hs):
  match hs:
    case []:
      {==}
    case _h <> _t:
      {==}

def Laws.lock_needed(_n):
  {==}

def Laws.lock_names(_deps, _h, _t):
  {==}

# ---------------------------------------------------------------------------
# EZ-OUT-1

# LAW: a plan ends with the status of whether it fails the command
law plan_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(DP.refuses.plan(pl)) : U32}

def plan_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.doctor_exits_as_it_fails(w):
  plan_code(DP.plan(w))

# ---------------------------------------------------------------------------
# EZ-VEN-6
#
# The lock check's lines stand after the library's and before the drift
# report, so a line the check says is said by doctor (`said_check`), and a
# check line that is a problem fails it (`wrong_check`). What the check says
# is found by rewriting the World's lock, its sources and the lock planner's
# open questions and decision to what each law assumes, after which the check
# is one note computed.

# LAW: one step of the front, with its head decided
law said_left.step:
  for bb: Bool
  for +t: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for +line: String
  for e: {DP.has.step(bb, _u => DP.said.in(DP.says(t), line)) == True{} : Bool}
  for ih: {DP.said.in(DP.says(t), line) == True{} : Bool}
    -> {DP.said.in(DP.says(List.append(&2, DP.Note, t, b)), line) == True{} : Bool}
  {DP.has.step(bb, _u => DP.said.in(DP.says(List.append(&2, DP.Note, t, b)), line)) == True{}
    : Bool}

def said_left.step(bb, _t, _b, _line, e, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: a line said by the first lines is said by all of them
law said_append_left:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(a), line) == True{} : Bool}
  {DP.said.in(DP.says(List.append(&2, DP.Note, a, b)), line) == True{} : Bool}

def said_append_left(a, b, line, e):
  match a:
    case []:
      Eq.bit.absurd(&2,
        {DP.said.in(DP.says(List.append(&2, DP.Note, [], b)), line) == True{} : Bool}, e)
    case h <> +t:
      match h:
        case DP.Note{_w, +l}:
          said_left.step(String.eq(l, line), t, b, line, e,
            z => said_append_left(t, b, line, z))

# LAW: a line the lock check says is said by doctor
law said_check:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(cs), line) == True{} : Bool}
  {DP.said.in(DP.says(DP.notes.of(led, got, cc, lib, lock, rs, cs)), line) == True{} : Bool}

def said_check(led, got, cc, lib, lock, rs, cs, line, e):
  said_append_left(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got), line,
    said_append(DP.probes(DP.programs(cc), rs),
      List.append(&2, DP.Note,
        [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
          DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
      line,
      said_append(
        [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
          DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
        line, e)))

# LAW: and a lock check line that is a problem fails doctor
law wrong_check:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for e: {DP.wrong(cs) == True{} : Bool}
  {DP.refuses.plan(DP.plan.notes(DP.notes.of(led, got, cc, lib, lock, rs, cs))) == True{} : Bool}

def wrong_check(led, got, cc, lib, lock, rs, cs, e):
  refuses_wrong(DP.notes.of(led, got, cc, lib, lock, rs, cs),
    wrong_append_left(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got),
      wrong_append(DP.probes(DP.programs(cc), rs),
        List.append(&2, DP.Note,
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
        wrong_append(
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
          e))))

# LAW: a note alone says its own line
law said_one:
  for +b: Bool
  for +line: String
  {DP.said.in(DP.says([DP.Note{b, line}]), line) == True{} : Bool}

def said_one(_b, line):
  step_hit(String.eq(line, line), _u => DP.said.in(DP.says([]), line),
    Eq.string_eq_self(line))

# LAW: over any World the lock planner asks nothing more of, about packages
# or names, the check's one line is the lock planner's verdict on the text:
# up to date when it decides on that text
law away_fresh:
  for +lw: W.World
  for +t: String
  for o: {[] == P.wants(lw) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(lw) : List<&2, W.Ask>}
  for d: {P.Doc{t} == P.decide(W.inputs(lw)) : P.Doc}
  {[DP.fresh.away(P.wants(lw), lw, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}

def away_fresh(lw, t, o, on, d):
  %o : {[DP.fresh.away(_, lw, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %on : {[DP.fresh.named(_, lw, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %d : {[DP.fresh.doc(_, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %Equal.sym(Bool, String.eq(t, t), True{}, Eq.string_eq_self(t))
    : {[DP.fresh.said(_)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  {==}

# LAW: and out of date when it decides on another
law away_stale:
  for +lw: W.World
  for +t: String
  for +u: String
  for o: {[] == P.wants(lw) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(lw) : List<&2, W.Ask>}
  for d: {P.Doc{u} == P.decide(W.inputs(lw)) : P.Doc}
  for ne: {False{} == String.eq(u, t) : Bool}
  {[DP.fresh.away(P.wants(lw), lw, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}

def away_stale(lw, t, _u, o, on, d, ne):
  %o : {[DP.fresh.away(_, lw, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %on : {[DP.fresh.named(_, lw, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %d : {[DP.fresh.doc(_, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %ne : {[DP.fresh.said(_)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  {==}

# LAW: a World the lock planner still asks about a package makes the line a
# problem
law away_asks:
  for +lw: W.World
  for +t: String
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for o: {a <> as == P.wants(lw) : List<&2, W.Ask>}
  {DP.wrong([DP.fresh.away(P.wants(lw), lw, t)]) == True{} : Bool}

def away_asks(lw, t, _a, _as, o):
  %o : {DP.wrong([DP.fresh.away(_, lw, t)]) == True{} : Bool}
  {==}

# LAW: and so does one it still asks about a name
law away_names:
  for +lw: W.World
  for +t: String
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for o: {[] == P.wants(lw) : List<&2, W.Ask>}
  for on: {a <> as == P.wants.names(lw) : List<&2, W.Ask>}
  {DP.wrong([DP.fresh.away(P.wants(lw), lw, t)]) == True{} : Bool}

def away_names(lw, t, _a, _as, o, on):
  %o : {DP.wrong([DP.fresh.away(_, lw, t)]) == True{} : Bool}
  %on : {DP.wrong([DP.fresh.named(_, lw, t)]) == True{} : Bool}
  {==}

def Laws.doctor_passes_fresh_lock(w, t, fs, k, l, o, on, d):
  %k : {DP.fresh.notes(_, w) == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %l : {DP.fresh.heard(_, w, t) == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  away_fresh(DP.relock(w, fs), t, o, on, d)

# LAW: the check's one line, for a lock that differs from the one decided on
law checked_stale:
  for +w: DW.World
  for +t: String
  for +u: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{u} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  for ne: {False{} == String.eq(u, t) : Bool}
  {DP.checked(w) == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}

def checked_stale(w, t, u, fs, k, l, o, on, d, ne):
  %k : {DP.fresh.notes(_, w) == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %l : {DP.fresh.heard(_, w, t) == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  away_stale(DP.relock(w, fs), t, u, o, on, d, ne)

def Laws.doctor_says_fresh_lock(w, t, fs, k, l, o, on, d):
  said_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), DP.fresh.line(),
    Equal.trans(Bool, DP.said.in(DP.says(DP.checked(w)), DP.fresh.line()),
      DP.said.in(DP.says([DP.Note{False{}, DP.fresh.line()}]), DP.fresh.line()), True{},
      Equal.cong(List<&2, DP.Note>, Bool, ns => DP.said.in(DP.says(ns), DP.fresh.line()),
        DP.checked(w), [DP.Note{False{}, DP.fresh.line()}],
        Laws.doctor_passes_fresh_lock(w, t, fs, k, l, o, on, d)),
      said_one(False{}, DP.fresh.line())))

def Laws.doctor_reports_stale_lock(w, t, u, fs, k, l, o, on, d, ne):
  said_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), DP.stale.line(),
    Equal.trans(Bool, DP.said.in(DP.says(DP.checked(w)), DP.stale.line()),
      DP.said.in(DP.says([DP.Note{True{}, DP.stale.line()}]), DP.stale.line()), True{},
      Equal.cong(List<&2, DP.Note>, Bool, ns => DP.said.in(DP.says(ns), DP.stale.line()),
        DP.checked(w), [DP.Note{True{}, DP.stale.line()}],
        checked_stale(w, t, u, fs, k, l, o, on, d, ne)),
      said_one(True{}, DP.stale.line())))

def Laws.doctor_stale_lock_fails(w, t, u, fs, k, l, o, on, d, ne):
  wrong_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w),
    Equal.trans(Bool, DP.wrong(DP.checked(w)), DP.wrong([DP.Note{True{}, DP.stale.line()}]), True{},
      Equal.cong(List<&2, DP.Note>, Bool, ns => DP.wrong(ns),
        DP.checked(w), [DP.Note{True{}, DP.stale.line()}],
        checked_stale(w, t, u, fs, k, l, o, on, d, ne)),
      {==}))

# LAW: a lock the lock planner still has questions about is a problem
law checked_away:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {a <> as == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.wrong(DP.checked(w)) == True{} : Bool}

def checked_away(w, t, fs, a, as, k, l, o):
  %k : {DP.wrong(DP.fresh.notes(_, w)) == True{} : Bool}
  %l : {DP.wrong(DP.fresh.heard(_, w, t)) == True{} : Bool}
  away_asks(DP.relock(w, fs), t, a, as, o)

def Laws.doctor_unchecked_lock_fails(w, t, fs, a, as, k, l, o):
  wrong_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), checked_away(w, t, fs, a, as, k, l, o))

# LAW: a lock the lock planner still asks a name's hash about is a problem
law checked_names_away:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {a <> as == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.wrong(DP.checked(w)) == True{} : Bool}

def checked_names_away(w, t, fs, a, as, k, l, o, on):
  %k : {DP.wrong(DP.fresh.notes(_, w)) == True{} : Bool}
  %l : {DP.wrong(DP.fresh.heard(_, w, t)) == True{} : Bool}
  away_names(DP.relock(w, fs), t, a, as, o, on)

def Laws.doctor_unchecked_names_fail(w, t, fs, a, as, k, l, o, on):
  wrong_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w),
    checked_names_away(w, t, fs, a, as, k, l, o, on))

# ---------------------------------------------------------------------------
# names files

# LAW: the library's line is a problem when one of its checks failed,
# whatever the other said
law lib_said_bad:
  for a: Bool
  for +dir: String
  for +count: Nat
  for +names: Nat
  for gone: List<&2, String>
  for bad: List<&2, String>
  {DP.note.wrong(DP.lib.said(Bool.and(a, False{}), dir, count, names, gone, bad)) == True{} : Bool}

def lib_said_bad(a, _dir, _count, _names, _gone, _bad):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: and a name whose file is wrong makes it one
law lib_names_bad:
  for +dir: String
  for +want: List<&2, String>
  for +ns: List<&2, L.Name>
  for +have: List<&2, String>
  for +rs: List<&2, DW.Reply>
  for +x: String
  for +xs: List<&2, String>
  for b: {x <> xs == DP.names.wrong(ns, rs) : List<&2, String>}
  {DP.note.wrong(DP.lib.judge(dir, want, ns, have, rs)) == True{} : Bool}

def lib_names_bad(dir, want, ns, have, _rs, x, xs, b):
  %b : {DP.note.wrong(DP.lib.said(
    Bool.and(List.is_empty(&2, String, DP.missing(want, have)), List.is_empty(&2, String, _)),
    dir, List.length(&2, String, want), List.length(&2, L.Name, ns), DP.missing(want, have), _))
    == True{} : Bool}
  lib_said_bad(List.is_empty(&2, String, DP.missing(want, have)), dir,
    List.length(&2, String, want), List.length(&2, L.Name, ns), DP.missing(want, have), x <> xs)

# LAW: three lines whose last is a problem have one
law wrong_third:
  for +n1: DP.Note
  for +n2: DP.Note
  for +n3: DP.Note
  for e: {DP.note.wrong(n3) == True{} : Bool}
  {DP.wrong([n1, n2, n3]) == True{} : Bool}

def wrong_third(n1, n2, n3, e):
  step_true(DP.note.wrong(n1), _u => DP.wrong([n2, n3]),
    step_true(DP.note.wrong(n2), _u => DP.wrong([n3]),
      step_hit(DP.note.wrong(n3), _u => DP.wrong([]), e)))

# LAW: a library line that is a problem fails doctor
law wrong_lib:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for +x: String
  for +xs: List<&2, String>
  for b: {x <> xs == DP.names.wrong(DP.lock.names(lock), rs) : List<&2, String>}
  {DP.refuses.plan(DP.plan.notes(DP.notes.of(led, got, cc, lib, lock, rs, cs))) == True{} : Bool}

def wrong_lib(led, got, cc, lib, lock, rs, cs, x, xs, b):
  refuses_wrong(DP.notes.of(led, got, cc, lib, lock, rs, cs),
    wrong_append_left(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got),
      wrong_append(DP.probes(DP.programs(cc), rs),
        List.append(&2, DP.Note,
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
        wrong_append_left(
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
          wrong_third(DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs),
            lib_names_bad(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock),
              DP.lib.have(DW.heard(rs, DW.Lib{DP.lib.at(lib)})), rs, x, xs, b))))))

def Laws.doctor_wrong_name_fails(w, x, xs, b):
  wrong_lib(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), x, xs, b)
