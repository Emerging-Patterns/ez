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
import ../manifest/manifest.bend as M
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
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w)))

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
  for +line: String
  for e: {DP.said.in(DP.says(DP.imports.notes(led, got)), line) == True{} : Bool}
  {DP.said.in(DP.says(DP.notes.of(led, got, cc, lib, lock, rs)), line) == True{} : Bool}

def said_notes(led, got, cc, lib, lock, rs, line, e):
  said_append(DP.head.notes(led, cc, lib, lock, rs), DP.imports.notes(led, got), line, e)

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
  for +e: {False{} == DP.has(hs, M.dep.hash(d)) : Bool}
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
      unused_put(DP.has(hs, M.dep.hash(x)), x,
        DP.unused(List.append(&2, M.Dep, t, d <> post), hs), DP.unused.line(d),
        unused_has(t, d, post, hs, e))

# ---------------------------------------------------------------------------
# EZ-VEN-5

def Laws.doctor_reports_unrecorded(w, n, e, b, hub, ds, _ts, fs, h, g, l, i, u):
  %g : {DP.said(DP.plan.of(DP.ledger.seen(_), DW.cc(w), DW.lib(w), DW.lock(w),
    DW.replies(w)), DP.unrecorded.line(h)) == True{} : Bool}
  %l : {DP.said.in(DP.says(DP.notes.of(M.Good{M.Manifest{n, e, b, hub, ds, []}}, _,
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w))), DP.unrecorded.line(h)) == True{}
    : Bool}
  said_notes(M.Good{M.Manifest{n, e, b, hub, ds, []}}, DW.Heard{DW.Listed{W.Listed{fs}}},
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.unrecorded.line(h),
    said_drift(DP.imports(fs), DP.drift(DP.imports(fs), ds), DP.unrecorded.line(h),
      has_append_left(DP.unrecorded(DP.missing(DP.imports(fs), DP.pinned(ds))),
        DP.unused(ds, DP.imports(fs)), DP.unrecorded.line(h),
        unrecorded_has(DP.missing(DP.imports(fs), DP.pinned(ds)), h,
          missing_has(DP.imports(fs), DP.pinned(ds), h,
            Equal.trans(Bool, DP.has(DP.imports(fs), h), DP.has(P.roots(fs), h), True{},
              once_has(P.roots(fs), h), i),
            u)))))

def Laws.doctor_reports_unused(w, n, e, b, hub, pre, d, post, _ts, fs, g, l, u):
  %g : {DP.said(DP.plan.of(DP.ledger.seen(_), DW.cc(w), DW.lib(w), DW.lock(w),
    DW.replies(w)), DP.unused.line(d)) == True{} : Bool}
  %l : {DP.said.in(DP.says(DP.notes.of(
    M.Good{M.Manifest{n, e, b, hub, List.append(&2, M.Dep, pre, d <> post), []}}, _,
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w))), DP.unused.line(d)) == True{} : Bool}
  said_notes(M.Good{M.Manifest{n, e, b, hub, List.append(&2, M.Dep, pre, d <> post), []}},
    DW.Heard{DW.Listed{W.Listed{fs}}},
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.unused.line(d),
    said_drift(DP.imports(fs),
      DP.drift(DP.imports(fs), List.append(&2, M.Dep, pre, d <> post)), DP.unused.line(d),
      has_append_right(
        DP.unrecorded(DP.missing(DP.imports(fs),
          DP.pinned(List.append(&2, M.Dep, pre, d <> post)))),
        DP.unused(List.append(&2, M.Dep, pre, d <> post), DP.imports(fs)),
        DP.unused.line(d),
        unused_has(pre, d, post, DP.imports(fs),
          Equal.trans(Bool, False{}, DP.has(P.roots(fs), M.dep.hash(d)),
            DP.has(DP.imports(fs), M.dep.hash(d)), u,
            Equal.sym(Bool, DP.has(DP.imports(fs), M.dep.hash(d)),
              DP.has(P.roots(fs), M.dep.hash(d)), once_has(P.roots(fs), M.dep.hash(d))))))))

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

def Laws.doctor_drift_fails(w, n, e, b, hub, ds, _ts, fs, x, xs, g, l, r):
  %g : {DP.refuses.plan(DP.plan.of(DP.ledger.seen(_), DW.cc(w), DW.lib(w), DW.lock(w),
    DW.replies(w))) == True{} : Bool}
  %l : {DP.refuses.plan(DP.plan.notes(DP.notes.of(M.Good{M.Manifest{n, e, b, hub, ds, []}},
    _, DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w)))) == True{} : Bool}
  %Equal.sym(List<&2, String>, DP.drift.of(fs, ds), x <> xs, r)
    : {DP.refuses.plan(DP.plan.notes(List.append(&2, DP.Note,
      DP.head.notes(M.Good{M.Manifest{n, e, b, hub, ds, []}}, DW.cc(w), DW.lib(w), DW.lock(w),
        DW.replies(w)),
      DP.drift.notes(DP.imports(fs), _)))) == True{} : Bool}
  refuses_wrong(List.append(&2, DP.Note,
      DP.head.notes(M.Good{M.Manifest{n, e, b, hub, ds, []}}, DW.cc(w), DW.lib(w), DW.lock(w),
        DW.replies(w)),
      DP.flag(x <> xs)),
    wrong_append(DP.head.notes(M.Good{M.Manifest{n, e, b, hub, ds, []}}, DW.cc(w), DW.lib(w),
      DW.lock(w), DW.replies(w)), DP.flag(x <> xs), {==}))

# ---------------------------------------------------------------------------
# a ledger that is not there, or not read

# LAW: doctor fails on a ledger it could not read, whatever else it found
law bad_fails:
  for +why: String
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  {DP.refuses.plan(DP.plan.of(M.Bad{why}, cc, lib, lock, rs)) == True{} : Bool}

def bad_fails(why, cc, lib, lock, rs):
  refuses_wrong(DP.notes.of(M.Bad{why}, DW.heard(rs, DW.Sources{}), cc, lib, lock, rs),
    wrong_append_left(DP.head.notes(M.Bad{why}, cc, lib, lock, rs),
      DP.imports.notes(M.Bad{why}, DW.heard(rs, DW.Sources{})),
      wrong_append(DP.probes(DP.programs(cc), rs),
        [DP.ledger.note(M.Bad{why}), DP.lock.note(0n, DP.locked.of(lock)),
          DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), rs)],
        {==})))

def Laws.doctor_needs_ledger(cc, lib, lock, rs):
  bad_fails("none here; ez init makes one", cc, lib, lock, rs)

def Laws.doctor_refuses_unread(cc, lib, lock, rs, _s, why, bad):
  %bad : {DP.refuses.plan(DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs)) == True{}
    : Bool}
  bad_fails(why, cc, lib, lock, rs)

# ---------------------------------------------------------------------------
# EZ-LED-5

# Both ledgers are seen without their tools, which is the same ledger.
def Laws.doctor_ignores_tools(cc, lib, lock, rs, _t1, t2, n, e, b, hub, ds, ts1, _ts2, g1, g2):
  %g1 : {DP.step.of(DP.ledger.seen(_), cc, lib, lock, rs)
    == DP.step(DW.World{cc, lib, Some{t2}, lock, rs}) : DP.Step}
  %g2 : {DP.step.of(DP.ledger.seen(M.Good{M.Manifest{n, e, b, hub, ds, ts1}}), cc, lib, lock, rs)
    == DP.step.of(DP.ledger.seen(_), cc, lib, lock, rs) : DP.Step}
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
