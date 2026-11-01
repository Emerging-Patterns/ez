# proofs of laws/DoctorReportsDrift.bend
#
# The plan is `plan.notes` of every line doctor found: each line said, and
# the command failed when one is a problem. Every effect is a `Say`, so the
# law that doctor writes nothing is an induction over the lines. The drift
# report is the last part of the lines, after the toolchain, the ledger, the
# lock and the library, so a law about what doctor says of the drift is a
# law about that last part, carried through the ones before it by
# `said_append`; a law that doctor fails is `wrong_append` the same way. The
# report itself is list membership: a hash the source imports and the ledger
# lacks survives `missing`, and its line is in `unrecorded`; a dependency no
# import names keeps its line in `unused`. Membership is `DP.has`, whose
# step is decided by `String.eq`, so each lemma splits on that answer, and
# an answer of True is turned into equal strings by `string_eq_true`.
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../laws/DoctorReportsDrift.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

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
  M1.said_append(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got), line, e)

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
      M1.step_true(String.eq(y, x), _u => DP.has(List.append(&2, String, t, b), x),
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
          M1.step_hit(String.eq(x, h), _u => DP.has(DP.missing(t, known), h), eb)
    case False{}:
      match c:
        case True{}:
          ih(e1)
        case False{}:
          M1.step_true(String.eq(x, h), _u => DP.has(DP.missing(t, known), h), ih(e1))

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
      M1.step_hit(String.eq(DP.unrecorded.line(x), DP.unrecorded.line(h)),
        _u => DP.has(DP.unrecorded(t), DP.unrecorded.line(h)),
        line_eq(x, h, Str.string_eq_true(x, h, eb)))
    case False{}:
      M1.step_true(String.eq(DP.unrecorded.line(x), DP.unrecorded.line(h)),
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
      M1.step_true(String.eq(DP.unused.line(x), target), _u => DP.has(rest, target), ih)

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
      M1.step_hit(String.eq(DP.unused.line(d), DP.unused.line(d)),
        _u => DP.has(DP.unused(post, hs), DP.unused.line(d)),
        Eq.string_eq_self(DP.unused.line(d)))
    case +x <> +t:
      unused_put(DP.used(hs, x), x,
        DP.unused(List.append(&2, M.Dep, t, d <> post), hs), DP.unused.line(d),
        unused_has(t, d, post, hs, e))

# ---------------------------------------------------------------------------
# laws/DoctorReportsDrift.bend

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
  M1.refuses_wrong(List.append(&2, DP.Note,
      DP.head.notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, DW.cc(w), DW.lib(w), DW.lock(w),
        DW.replies(w), DP.checked(w)),
      DP.flag(x <> xs)),
    M1.wrong_append(DP.head.notes(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, []}}, DW.cc(w), DW.lib(w),
      DW.lock(w), DW.replies(w), DP.checked(w)), DP.flag(x <> xs), {==}))
