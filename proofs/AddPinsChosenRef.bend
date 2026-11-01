# proofs of laws/AddPinsChosenRef.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/manifest.bend as M
import ../src/git/git.bend as Git
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/ez/target.bend as Tgt
import ../laws/AddPinsChosenRef.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2
import ./lemmas/PlanEffectFacts.bend as M3

# LAW: with no ref, the tag recorded is the default one
law tag_default:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  {AP.tag(w) == AP.default.ref(w) : String}

def tag_default(w, none):
  %Equal.sym(String, A.ref(w), "", none) : {AP.tag.of(Git.is_rev(_), String.is_empty(_), w)
    == AP.default.ref(w) : String}
  {==}

def Laws.add_pins_chosen(w, none, ok):
  Equal.trans(String, M.source.tag(M.source.dep(AP.added(w))), AP.tag(w),
    AP.default.ref(w),
    Equal.cong(M.Dep, String, d => M.source.tag(M.source.dep(d)), AP.added(w),
      AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok)),
    tag_default(w, none))

# LAW: the checkout is no question about a ref
law co_resolves:
  for c: AP.Co
  for +rev: String
  for +f: String
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.co(c, rev)), f)) == False{} : Bool}

def co_resolves(c, _rev, _f):
  match c:
    case AP.Co{_nar, _fs}:
      {==}
    case AP.CoWait{}:
      {==}
    case AP.CoNo{_why}:
      {==}

# LAW: past the early refusals, a 40-hex ref asks only for the checkout
law early_resolves:
  for b: Bool
  for +why: String
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.early(b, why, w)), A.from(w))) == False{} : Bool}

def early_resolves(b, _why, w, hex):
  match b:
    case True{}:
      %Equal.sym(Bool, Git.is_rev(A.ref(w)), True{}, hex)
        : {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.tip(AP.tip.of(_,
          String.is_empty(A.ref(w)), w), w)), A.from(w))) == False{} : Bool}
      co_resolves(AP.co.at(w, A.ref(w)), A.ref(w), A.from(w))
    case False{}:
      {==}

law place_resolves:
  for p: Tgt.Place
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.place(p, w)), A.from(w))) == False{} : Bool}

def place_resolves(p, w, hex):
  match p:
    case Tgt.Bad{_why}:
      {==}
    case Tgt.Local{_path}:
      early_resolves(String.is_empty(AP.early(w)), AP.early(w), w, hex)
    case Tgt.Remote{_url, _slug}:
      early_resolves(String.is_empty(AP.early(w)), AP.early(w), w, hex)

law read_resolves:
  for r: M.Read
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.asks.of(AP.qs.v(AP.decide.read(r, w)), A.from(w))) == False{} : Bool}

def read_resolves(r, w, hex):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      place_resolves(A.place(w), w, hex)

def Laws.add_commit_asks_nothing(w, hex):
  read_resolves(A.read(w), w, hex)

# ---------------------------------------------------------------------------
# the commit pinned

# LAW: the commit a found rev gives is that rev, "" giving none
law found_rev:
  for +e: String
  for why: String
  {AP.tip.rev(AP.tip.found(e, why)) == e : String}

def found_rev(e, _why):
  match e:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# LAW: a named ref's commit is what `Git.exact` reads from what was printed
law named_rev:
  for s: Up.Said
  for +w: A.World
  {AP.tip.rev(AP.tip.refs(s, w))
    == Git.exact(Git.rows(String.lines(AP.said.text(s))), A.ref(w)) : String}

def named_rev(s, w):
  match s:
    case Up.Said{+text}:
      found_rev(Git.exact(Git.rows(String.lines(text)), A.ref(w)),
        "ez: " ++ A.url(w) ++ " has no ref named " ++ A.ref(w))
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law rev_named:
  for +w: A.World
  for nr: {Git.is_rev(A.ref(w)) == False{} : Bool}
  for ne: {String.is_empty(A.ref(w)) == False{} : Bool}
  {AP.rev(w) == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}

def rev_named(w, nr, ne):
  %Equal.sym(Bool, Git.is_rev(A.ref(w)), False{}, nr)
    : {AP.tip.rev(AP.tip.of(_, String.is_empty(A.ref(w)), w))
      == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}
  %Equal.sym(Bool, String.is_empty(A.ref(w)), False{}, ne)
    : {AP.tip.rev(AP.tip.of(False{}, _, w))
      == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}
  named_rev(AP.said(w, AP.QRefs{A.ref(w)}), w)

def Laws.add_pins_named(w, nr, ne, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w),
    Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok)),
    rev_named(w, nr, ne))

# LAW: the chosen tag's commit, when a tag was chosen
law chosen_rev:
  for s: Up.Said
  for +w: A.World
  for c: {String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(s))))))
    == False{} : Bool}
  {AP.tip.rev(AP.tip.tags(s, w)) == Git.exact(Git.rows(String.lines(AP.said.text(s))),
    Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(s)))))) : String}

def chosen_rev(s, w, c):
  match s:
    case Up.Said{+text}:
      %Equal.sym(Bool, String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))),
        False{}, c)
        : {AP.tip.rev(AP.tip.chosen(_, Git.choose(Git.tag.names(Git.rows(String.lines(text)))),
          Git.rows(String.lines(text)), w)) == Git.exact(Git.rows(String.lines(text)),
          Git.choose(Git.tag.names(Git.rows(String.lines(text))))) : String}
      found_rev(Git.exact(Git.rows(String.lines(text)),
        Git.choose(Git.tag.names(Git.rows(String.lines(text))))),
        "ez: " ++ A.url(w) ++ " has no tag named " ++
          Git.choose(Git.tag.names(Git.rows(String.lines(text)))))
    case Up.Unsaid{why}:
      Eq.bit.absurd2(&2, {AP.tip.rev(AP.tip.tags(Up.Unsaid{why}, w))
        == Git.exact(Git.rows(String.lines(AP.said.text(Up.Unsaid{why}))),
          Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(Up.Unsaid{why}))))))
        : String}, c)
    case Up.Unasked{ask}:
      Eq.bit.absurd2(&2, {AP.tip.rev(AP.tip.tags(Up.Unasked{ask}, w))
        == Git.exact(Git.rows(String.lines(AP.said.text(Up.Unasked{ask}))),
          Git.choose(Git.tag.names(Git.rows(String.lines(AP.said.text(Up.Unasked{ask}))))))
        : String}, c)

law rev_chosen:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for c: {String.is_empty(Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))) == False{}
    : Bool}
  {AP.rev(w) == Git.exact(AP.rows(w, AP.QTags{}),
    Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))) : String}

def rev_chosen(w, none, c):
  %Equal.sym(String, A.ref(w), "", none)
    : {AP.tip.rev(AP.tip.of(Git.is_rev(_), String.is_empty(_), w))
      == Git.exact(AP.rows(w, AP.QTags{}), Git.choose(Git.tag.names(AP.rows(w, AP.QTags{}))))
      : String}
  chosen_rev(AP.said(w, AP.QTags{}), w, c)

def Laws.add_pins_chosen_rev(w, none, c, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w),
    Git.exact(AP.rows(w, AP.QTags{}), Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok)),
    rev_chosen(w, none, c))

law rev_commit:
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.rev(w) == A.ref(w) : String}

def rev_commit(w, hex):
  %Equal.sym(Bool, Git.is_rev(A.ref(w)), True{}, hex)
    : {AP.tip.rev(AP.tip.of(_, String.is_empty(A.ref(w)), w)) == A.ref(w) : String}
  {==}

def Laws.add_pins_commit(w, hex, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w), A.ref(w),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok)),
    rev_commit(w, hex))

# LAW: HEAD's commit, when its symref names a branch
law head_rev:
  for s: Up.Said
  for +w: A.World
  for b: {String.is_empty(Git.tip.branch(Git.rows(String.lines(AP.said.text(s))))) == False{}
    : Bool}
  {AP.tip.rev(AP.tip.head(s, w)) == Git.tip.rev(Git.rows(String.lines(AP.said.text(s))))
    : String}

def head_rev(s, w, b):
  match s:
    case Up.Said{+text}:
      %Equal.sym(Bool, String.is_empty(Git.tip.branch(Git.rows(String.lines(text)))), False{}, b)
        : {AP.tip.rev(Bool.pick(AP.Tip, _,
          AP.TipNo{"ez: " ++ A.url(w) ++
            " has no semver-ish tag and its HEAD names no branch; name a ref to pin"},
          AP.tip.found(Git.tip.rev(Git.rows(String.lines(text))),
            "ez: " ++ A.url(w) ++ " has no HEAD")))
          == Git.tip.rev(Git.rows(String.lines(text))) : String}
      found_rev(Git.tip.rev(Git.rows(String.lines(text))), "ez: " ++ A.url(w) ++ " has no HEAD")
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law rev_head:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for +text: String
  for t: {AP.said(w, AP.QTags{}) == Up.Said{text} : Up.Said}
  for c: {String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))) == True{}
    : Bool}
  for b: {String.is_empty(Git.tip.branch(AP.rows(w, AP.QHead{}))) == False{} : Bool}
  {AP.rev(w) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}

def rev_head(w, none, text, t, c, b):
  %Equal.sym(String, A.ref(w), "", none)
    : {AP.tip.rev(AP.tip.of(Git.is_rev(_), String.is_empty(_), w))
      == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}
  %Equal.sym(Up.Said, AP.said(w, AP.QTags{}), Up.Said{text}, t)
    : {AP.tip.rev(AP.tip.tags(_, w)) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}
  %Equal.sym(Bool, String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))),
    True{}, c)
    : {AP.tip.rev(AP.tip.chosen(_, Git.choose(Git.tag.names(Git.rows(String.lines(text)))),
      Git.rows(String.lines(text)), w)) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}
  head_rev(AP.said(w, AP.QHead{}), w, b)

def Laws.add_pins_head_rev(w, none, text, t, c, b, ok):
  Equal.trans(String, M.source.rev(M.source.dep(AP.added(w))), AP.rev(w),
    Git.tip.rev(AP.rows(w, AP.QHead{})),
    Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)), AP.added(w),
      AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok)),
    rev_head(w, none, text, t, c, b))

# A ref's length or alphabet is rewritten into `Bool.and`. The two root
# laws rewrite a depth comparison into the climb count.

def Laws.is_rev_needs_40(ref, e):
  %e : {Bool.and(_, Git.hex.all(String.to_list(ref))) == False{} : Bool}
  {==}

def Laws.is_rev_needs_hex(ref, e0, e1):
  %e0 : {Bool.and(_, Git.hex.all(String.to_list(ref))) == False{} : Bool}
  %e1 : {_ == False{} : Bool}
  {==}

def Laws.is_rev_hex40(ref, e0, e1):
  %e0 : {Bool.and(_, Git.hex.all(String.to_list(ref))) == True{} : Bool}
  %e1 : {_ == True{} : Bool}
  {==}

# The tag choice. `latest.rel` folds the names from the right, and each step
# is one of three picks: pass a name over, take it because nothing after it
# was a release, or weigh it against the greatest release after it. Each pick
# is a match on a computed value, so each is lifted into a parameter with the
# equation that put it there, and the recursive call on the tail arrives as a
# function the arm applies only where the tail is what decides.

# LAW: a release has a name
law release_named:
  for +h: String
  for e: {Git.release(h) == True{} : Bool}
  {String.is_empty(h) == False{} : Bool}

def release_named(h, e):
  match h:
    case SNil{}:
      Eq.bit.absurd(&2, {String.is_empty(SNil{}) == False{} : Bool}, e)
    case SCon{_c, _t}:
      {==}

# LAW: a release weighed against another name comes out one of the two
law rel_ne.cmp:
  for +h: String
  for +r: String
  for d: Bool
  for ec: {String.is_empty(r) == False{} : Bool}
  for eb: {Git.release(h) == True{} : Bool}
  {String.is_empty(Git.latest.cmp(d, h, r)) == False{} : Bool}

def rel_ne.cmp(h, _r, d, ec, eb):
  match d:
    case True{}:
      release_named(h, eb)
    case False{}:
      ec

# LAW: a release taken or weighed leaves a name
law rel_ne.have:
  for +h: String
  for +r: String
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for eb: {Git.release(h) == True{} : Bool}
  {String.is_empty(Git.latest.have(c, h, r, Git.ver.of(h))) == False{} : Bool}

def rel_ne.have(h, r, c, ec, eb):
  match c:
    case True{}:
      release_named(h, eb)
    case False{}:
      rel_ne.cmp(h, r, Git.newer(Git.ord.ver(Git.ver.of(h), Git.ver.of(r))), ec, eb)

# LAW: one step of the fold, when some name from here on is a release
law rel_ne.arm:
  for +h: String
  for +t: List<&2, String>
  for b: Bool
  for eb: {Git.release(h) == b : Bool}
  for e: {Git.has.release.step(b, _u => Git.has.release(t)) == True{} : Bool}
  for ih: {Git.has.release(t) == True{} : Bool}
    -> {String.is_empty(Git.latest.rel(t)) == False{} : Bool}
  {String.is_empty(Git.latest.rel.step(b, h, Git.latest.rel(t))) == False{} : Bool}

def rel_ne.arm(h, t, b, eb, e, ih):
  match b:
    case False{}:
      ih(e)
    case True{}:
      rel_ne.have(h, Git.latest.rel(t), String.is_empty(Git.latest.rel(t)), {==}, eb)

# LAW: when some name is a release, the greatest release is a name
law rel_ne:
  for +names: List<&2, String>
  for e: {Git.has.release(names) == True{} : Bool}
  {String.is_empty(Git.latest.rel(names)) == False{} : Bool}

def rel_ne(names, e):
  match names:
    case []:
      Eq.bit.absurd(&2, {String.is_empty(Git.latest.rel([])) == False{} : Bool}, e)
    case +h <> t:
      rel_ne.arm(h, t, Git.release(h), {==}, e, x => rel_ne(t, x))

# LAW: a release weighed against another release comes out a release
law rel_is.cmp:
  for +h: String
  for +r: String
  for d: Bool
  for eb: {Git.release(h) == True{} : Bool}
  for er: {Git.release(r) == True{} : Bool}
  {Git.release(Git.latest.cmp(d, h, r)) == True{} : Bool}

def rel_is.cmp(_h, _r, d, eb, er):
  match d:
    case True{}:
      eb
    case False{}:
      er

# LAW: a release taken or weighed leaves a release
law rel_is.have:
  for +h: String
  for +r: String
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for eb: {Git.release(h) == True{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> {Git.release(r) == True{} : Bool}
  {Git.release(Git.latest.have(c, h, r, Git.ver.of(h))) == True{} : Bool}

def rel_is.have(h, r, c, ec, eb, ih):
  match c:
    case True{}:
      eb
    case False{}:
      rel_is.cmp(h, r, Git.newer(Git.ord.ver(Git.ver.of(h), Git.ver.of(r))), eb, ih(ec))

# LAW: one step of the fold, when what it answers is a name
law rel_is.arm:
  for +h: String
  for +t: List<&2, String>
  for b: Bool
  for eb: {Git.release(h) == b : Bool}
  for e: {String.is_empty(Git.latest.rel.step(b, h, Git.latest.rel(t))) == False{} : Bool}
  for ih: {String.is_empty(Git.latest.rel(t)) == False{} : Bool}
    -> {Git.release(Git.latest.rel(t)) == True{} : Bool}
  {Git.release(Git.latest.rel.step(b, h, Git.latest.rel(t))) == True{} : Bool}

def rel_is.arm(h, t, b, eb, e, ih):
  match b:
    case False{}:
      ih(e)
    case True{}:
      rel_is.have(h, Git.latest.rel(t), String.is_empty(Git.latest.rel(t)), {==}, eb, ih)

# LAW: whatever name the fold answers is a release
law rel_is:
  for +names: List<&2, String>
  for e: {String.is_empty(Git.latest.rel(names)) == False{} : Bool}
  {Git.release(Git.latest.rel(names)) == True{} : Bool}

def rel_is(names, e):
  match names:
    case []:
      Eq.bit.absurd2(&2, {Git.release(Git.latest.rel([])) == True{} : Bool}, e)
    case +h <> t:
      rel_is.arm(h, t, Git.release(h), {==}, e, x => rel_is(t, x))

# The choice is rewritten to the arm that takes the release, which the two
# lemmas say is there and is a release.
def Laws.choose_release(names, e):
  +ne = rel_ne(names, e)
  Equal.trans(Bool,
    Git.release(Git.choose.go(String.is_empty(Git.latest.rel(names)),
      Git.latest.rel(names), Git.latest(names))),
    Git.release(Git.choose.go(False{}, Git.latest.rel(names), Git.latest(names))),
    True{},
    Equal.cong(Bool, Bool,
      x => Git.release(Git.choose.go(x, Git.latest.rel(names), Git.latest(names))),
      String.is_empty(Git.latest.rel(names)), False{}, ne),
    rel_is(names, ne))

# LAW: one step of the fold, when no name from here on is a release
law rel_none.arm:
  for +h: String
  for +t: List<&2, String>
  for b: Bool
  for e: {Git.has.release.step(b, _u => Git.has.release(t)) == False{} : Bool}
  for ih: {Git.has.release(t) == False{} : Bool} -> {Git.latest.rel(t) == "" : String}
  {Git.latest.rel.step(b, h, Git.latest.rel(t)) == "" : String}

def rel_none.arm(h, t, b, e, ih):
  match b:
    case True{}:
      Eq.bit.absurd2(&2, {Git.latest.rel.step(True{}, h, Git.latest.rel(t)) == "" : String}, e)
    case False{}:
      ih(e)

# LAW: with no release among the names, the fold answers nothing
law rel_none:
  for +names: List<&2, String>
  for e: {Git.has.release(names) == False{} : Bool}
  {Git.latest.rel(names) == "" : String}

def rel_none(names, e):
  match names:
    case []:
      {==}
    case +h <> t:
      rel_none.arm(h, t, Git.release(h), e, x => rel_none(t, x))

def Laws.choose_prerelease(names, e):
  Equal.cong(String, String,
    x => Git.choose.go(String.is_empty(x), x, Git.latest(names)),
    Git.latest.rel(names), "", rel_none(names, e))

# The default branch. A symref row's branch is a literal prefix taken off a
# name that is not empty, so it computes once the name is a char and a rest.
# The other two rows are rewritten to the empty answer that passes them over.

def Laws.branch_of_symref(b, rest, e):
  match b:
    case SNil{}:
      Eq.bit.absurd(&2,
        {Git.tip.branch(Git.Row{"ref: refs/heads/", "HEAD"} <> rest) == "" : String}, e)
    case SCon{_c, _t}:
      {==}

def Laws.branch_skips_other(rev, _name, rest, e):
  %e : {Git.tip.step(String.is_empty(Git.tip.branch.pick(_, rev)),
    Git.tip.branch.pick(_, rev), _u => Git.tip.branch(rest)) == Git.tip.branch(rest)
    : String}
  {==}

def Laws.branch_skips_commit(rev, rest, e):
  %e : {Git.tip.step(
    String.is_empty(Git.tip.strip(Bool.pick(String, _,
      String.drop(rev, String.length("ref: ")), ""), "refs/heads/")),
    Git.tip.strip(Bool.pick(String, _,
      String.drop(rev, String.length("ref: ")), ""), "refs/heads/"),
    _u => Git.tip.branch(rest)) == Git.tip.branch(rest) : String}
  {==}

# The exact pick. A row is compared by its whole name against each of the
# three a ref may have, and each comparison the premises answer is rewritten
# to the arm that passes the row over.

def Laws.exact_skips(rev, name, rs, ref, e0, e1, e2):
  %e0 : {Git.or_else(
    Git.named.step(_, rev, _u => Git.named(rs, "refs/tags/" ++ ref ++ "^{}")),
    Git.or_else(
      Git.named.step(String.eq(name, "refs/tags/" ++ ref), rev,
        _u => Git.named(rs, "refs/tags/" ++ ref)),
      Git.named.step(String.eq(name, "refs/heads/" ++ ref), rev,
        _u => Git.named(rs, "refs/heads/" ++ ref))))
    == Git.exact(rs, ref) : String}
  %e1 : {Git.or_else(
    Git.named.step(False{}, rev, _u => Git.named(rs, "refs/tags/" ++ ref ++ "^{}")),
    Git.or_else(
      Git.named.step(_, rev, _u => Git.named(rs, "refs/tags/" ++ ref)),
      Git.named.step(String.eq(name, "refs/heads/" ++ ref), rev,
        _u => Git.named(rs, "refs/heads/" ++ ref))))
    == Git.exact(rs, ref) : String}
  %e2 : {Git.or_else(
    Git.named.step(False{}, rev, _u => Git.named(rs, "refs/tags/" ++ ref ++ "^{}")),
    Git.or_else(
      Git.named.step(False{}, rev, _u => Git.named(rs, "refs/tags/" ++ ref)),
      Git.named.step(_, rev, _u => Git.named(rs, "refs/heads/" ++ ref))))
    == Git.exact(rs, ref) : String}
  {==}

def Laws.exact_tag_first(rs, ref, e):
  %e : {Git.or_else(Git.named(rs, "refs/tags/" ++ ref ++ "^{}"),
    Bool.pick(String, _, Git.named(rs, "refs/heads/" ++ ref),
      Git.named(rs, "refs/tags/" ++ ref)))
    == Git.or_else(Git.named(rs, "refs/tags/" ++ ref ++ "^{}"),
      Git.named(rs, "refs/tags/" ++ ref)) : String}
  {==}

def Laws.exact_branch(rs, ref, e0, e1):
  %e0 : {Git.or_else(_, Git.or_else(Git.named(rs, "refs/tags/" ++ ref),
    Git.named(rs, "refs/heads/" ++ ref))) == Git.named(rs, "refs/heads/" ++ ref)
    : String}
  %e1 : {Git.or_else("", Git.or_else(_, Git.named(rs, "refs/heads/" ++ ref)))
    == Git.named(rs, "refs/heads/" ++ ref) : String}
  {==}

# LAW: a number is EQ to itself
law nat.refl:
  for +a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

def nat.refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      nat.refl(p)

# LAW: dotted numbers are EQ to themselves
law nums.refl:
  for +a: List<&2, Nat>
  {M2.nums.c(a, a) == EQ{} : Cmp}

def nums.refl(a):
  match a:
    case []:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Cmp, Nat.cmp(h, h), EQ{}, nat.refl(h))
        : {M2.cmp.lex(_, M2.nums.c(t, t)) == EQ{} : Cmp}
      nums.refl(t)

# LAW: an identifier is EQ to itself
law id.refl:
  for +x: Git.Id
  {M2.id.c(x, x) == EQ{} : Cmp}

def id.refl(x):
  match x:
    case Git.IdNum{+n}:
      nat.refl(n)
    case Git.IdWord{+s}:
      Eq.string_order_self(s)

# LAW: an identifier list is EQ to itself
law ids.refl:
  for +xs: List<&2, Git.Id>
  {M2.ids.c(xs, xs) == EQ{} : Cmp}

def ids.refl(xs):
  match xs:
    case []:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Cmp, M2.id.c(h, h), EQ{}, id.refl(h))
        : {M2.cmp.lex(_, M2.ids.c(t, t)) == EQ{} : Cmp}
      ids.refl(t)

# LAW: a pre-release is EQ to itself
law rel.refl:
  for +p: List<&2, Git.Id>
  {M2.rel.c(p, p) == EQ{} : Cmp}

def rel.refl(p):
  match p:
    case []:
      {==}
    case Con{+h, +t}:
      ids.refl(h <> t)

# LAW: a version is EQ to itself
law ver.refl:
  for +na: List<&2, Nat>
  for +pa: List<&2, Git.Id>
  {M2.ver.c(na, pa, na, pa) == EQ{} : Cmp}

def ver.refl(na, pa):
  %Equal.sym(Cmp, M2.nums.c(na, na), EQ{}, nums.refl(na))
    : {M2.cmp.lex(_, M2.rel.c(pa, pa)) == EQ{} : Cmp}
  rel.refl(pa)

# LAW: the same over any three versions. A name that is not semver-ish is
# newer than nothing and nothing is newer than it, so only three semver-ish
# versions have anything to say.
law top.go:
  for +vn: Git.Ver
  for +vh: Git.Ver
  for +vr: Git.Ver
  for ea: {Git.newer(Git.ord.ver(vn, vr)) == False{} : Bool}
  for eb: {Git.newer(Git.ord.ver(vh, vr)) == True{} : Bool}
  {Git.newer(Git.ord.ver(vn, vh)) == False{} : Bool}

def top.go(vn, vh, vr, ea, eb):
  match vn vh vr:
    case Git.No{} _ _:
      {==}
    case Git.Yes{_na, _pa} Git.No{} _:
      Eq.bit.absurd(&2, {Git.newer(Git.ord.ver(Git.Yes{_na, _pa}, Git.No{})) == False{}
        : Bool}, eb)
    case Git.Yes{_na, _pa} Git.Yes{_nb, _pb} Git.No{}:
      Eq.bit.absurd(&2, {Git.newer(Git.ord.ver(Git.Yes{_na, _pa}, Git.Yes{_nb, _pb}))
        == False{} : Bool}, eb)
    case Git.Yes{+na, +pa} Git.Yes{+nb, +pb} Git.Yes{+nc, +pc}:
      M2.ver.below(na, pa, nb, pb, nc, pc, ea, eb)

# LAW: no version is newer than itself
law self.go:
  for +v: Git.Ver
  {Git.newer(Git.ord.ver(v, v)) == False{} : Bool}

def self.go(v):
  match v:
    case Git.No{}:
      {==}
    case Git.Yes{+n, +p}:
      %Equal.sym(Bool, Git.newer(Git.ord.ver(Git.Yes{n, p}, Git.Yes{n, p})),
        Cmp.is_gt(M2.ver.c(n, p, n, p)), M2.newer_ver(n, p, n, p))
        : {_ == False{} : Bool}
      %Equal.sym(Cmp, M2.ver.c(n, p, n, p), EQ{}, ver.refl(n, p))
        : {Cmp.is_gt(_) == False{} : Bool}
      {==}

# LAW: a name weighed against a name leaves a name
law ne.cmp:
  for +n: String
  for +r: String
  for d: Bool
  for ec: {String.is_empty(r) == False{} : Bool}
  for nn: {String.is_empty(n) == False{} : Bool}
  {String.is_empty(Git.latest.cmp(d, n, r)) == False{} : Bool}

def ne.cmp(_n, _r, d, ec, nn):
  match d:
    case True{}:
      nn
    case False{}:
      ec

# LAW: a name taken or weighed leaves a name
law ne.have:
  for +n: String
  for +r: String
  for +v: Git.Ver
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for nn: {String.is_empty(n) == False{} : Bool}
  {String.is_empty(Git.latest.have(c, n, r, v)) == False{} : Bool}

def ne.have(n, r, v, c, ec, nn):
  match c:
    case True{}:
      nn
    case False{}:
      ne.cmp(n, r, Git.newer(Git.ord.ver(v, Git.ver.of(r))), ec, nn)

# LAW: the fold's step at `n` leaves a name
law ne.head:
  for +n: String
  for +r: String
  for +v: Git.Ver
  for ev: {Git.ver.of(n) == v : Git.Ver}
  for ns: List<&2, Nat>
  for ps: List<&2, Git.Id>
  for evn: {Git.ver.of(n) == Git.Yes{ns, ps} : Git.Ver}
  {String.is_empty(Git.latest.step(v, n, r)) == False{} : Bool}

def ne.head(n, r, v, ev, ns, ps, evn):
  match v:
    case Git.No{}:
      Eq.bit.gone(&2, {String.is_empty(Git.latest.step(Git.No{}, n, r)) == False{}
        : Bool}, M2.ver.clash(ns, ps,
          Equal.trans(Git.Ver, Git.No{}, Git.ver.of(n), Git.Yes{ns, ps},
            Equal.sym(Git.Ver, Git.ver.of(n), Git.No{}, ev), evn)))
    case Git.Yes{+a, +b}:
      ne.have(n, r, Git.Yes{a, b}, String.is_empty(r), {==}, M2.named(n, a, b, ev))

# LAW: a step past `n` keeps a name
law ne.tail:
  for +h: String
  for +r: String
  for +v: Git.Ver
  for ev: {Git.ver.of(h) == v : Git.Ver}
  for ih: {String.is_empty(r) == False{} : Bool}
  {String.is_empty(Git.latest.step(v, h, r)) == False{} : Bool}

def ne.tail(h, r, v, ev, ih):
  match v:
    case Git.No{}:
      ih
    case Git.Yes{+a, +b}:
      ne.have(h, r, Git.Yes{a, b}, String.is_empty(r), {==}, M2.named(h, a, b, ev))

# LAW: with a semver-ish tag in the list, `latest` answers a name
law latest.ne:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for ns: List<&2, Nat>
  for ps: List<&2, Git.Id>
  for ev: {Git.ver.of(n) == Git.Yes{ns, ps} : Git.Ver}
  {String.is_empty(Git.latest(List.append(&2, String, xs, n <> ys))) == False{}
    : Bool}

def latest.ne(xs, n, ys, ns, ps, ev):
  match xs:
    case []:
      ne.head(n, Git.latest(ys), Git.ver.of(n), {==}, ns, ps, ev)
    case +h <> t:
      ne.tail(h, Git.latest(List.append(&2, String, t, n <> ys)), Git.ver.of(h), {==},
        latest.ne(t, n, ys, ns, ps, ev))

# LAW: weighing `n` against what the fold holds keeps nothing newer than `n`
law head.cmp:
  for +n: String
  for +r: String
  for +vn: Git.Ver
  for ev: {Git.ver.of(n) == vn : Git.Ver}
  for d: Bool
  for ed: {Git.newer(Git.ord.ver(vn, Git.ver.of(r))) == d : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.cmp(d, n, r)))) == False{}
    : Bool}

def head.cmp(n, r, vn, ev, d, ed):
  match d:
    case True{}:
      self.go(Git.ver.of(n))
    case False{}:
      %Equal.sym(Git.Ver, Git.ver.of(n), vn, ev)
        : {Git.newer(Git.ord.ver(_, Git.ver.of(r))) == False{} : Bool}
      ed

# LAW: and so does taking `n` when the fold holds nothing
law head.have:
  for +n: String
  for +r: String
  for +vn: Git.Ver
  for ev: {Git.ver.of(n) == vn : Git.Ver}
  for c: Bool
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.have(c, n, r, vn))))
    == False{} : Bool}

def head.have(n, r, vn, ev, c):
  match c:
    case True{}:
      self.go(Git.ver.of(n))
    case False{}:
      head.cmp(n, r, vn, ev, Git.newer(Git.ord.ver(vn, Git.ver.of(r))), {==})

# LAW: the fold's step at `n` holds nothing newer than `n`
law head.step:
  for +n: String
  for +r: String
  for +v: Git.Ver
  for ev: {Git.ver.of(n) == v : Git.Ver}
  for ns: List<&2, Nat>
  for ps: List<&2, Git.Id>
  for evn: {Git.ver.of(n) == Git.Yes{ns, ps} : Git.Ver}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.step(v, n, r)))) == False{}
    : Bool}

def head.step(n, r, v, ev, ns, ps, evn):
  match v:
    case Git.No{}:
      Eq.bit.gone(&2, {Git.newer(Git.ord.ver(Git.ver.of(n),
        Git.ver.of(Git.latest.step(Git.No{}, n, r)))) == False{} : Bool},
        M2.ver.clash(ns, ps,
          Equal.trans(Git.Ver, Git.No{}, Git.ver.of(n), Git.Yes{ns, ps},
            Equal.sym(Git.Ver, Git.ver.of(n), Git.No{}, ev), evn)))
    case Git.Yes{+a, +b}:
      head.have(n, r, Git.Yes{a, b}, ev, String.is_empty(r))

# LAW: a name after `n` that replaces what the fold holds is newer than it,
# so `n` stays below
law have.cmp:
  for +h: String
  for +r: String
  for +n: String
  for +vh: Git.Ver
  for evh: {Git.ver.of(h) == vh : Git.Ver}
  for d: Bool
  for ed: {Git.newer(Git.ord.ver(vh, Git.ver.of(r))) == d : Bool}
  for ih: {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(r))) == False{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.cmp(d, h, r)))) == False{}
    : Bool}

def have.cmp(h, r, n, vh, evh, d, ed, ih):
  match d:
    case False{}:
      ih
    case True{}:
      %Equal.sym(Git.Ver, Git.ver.of(h), vh, evh)
        : {Git.newer(Git.ord.ver(Git.ver.of(n), _)) == False{} : Bool}
      top.go(Git.ver.of(n), vh, Git.ver.of(r), ih, ed)

# LAW: weighing a name after `n` against a name the fold holds keeps `n` below
law have.top:
  for +h: String
  for +r: String
  for +n: String
  for +vh: Git.Ver
  for evh: {Git.ver.of(h) == vh : Git.Ver}
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for ne: {String.is_empty(r) == False{} : Bool}
  for ih: {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(r))) == False{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.have(c, h, r, vh))))
    == False{} : Bool}

def have.top(h, r, n, vh, evh, c, ec, ne, ih):
  match c:
    case True{}:
      Eq.bit.absurd2(&2, {Git.newer(Git.ord.ver(Git.ver.of(n),
        Git.ver.of(Git.latest.have(True{}, h, r, vh)))) == False{} : Bool},
        Equal.trans(Bool, True{}, String.is_empty(r), False{},
          Equal.sym(Bool, String.is_empty(r), True{}, ec), ne))
    case False{}:
      have.cmp(h, r, n, vh, evh, Git.newer(Git.ord.ver(vh, Git.ver.of(r))), {==}, ih)

# LAW: a step of `latest` past `n` keeps `n` below
law tail.step:
  for +h: String
  for +r: String
  for +n: String
  for +v: Git.Ver
  for ev: {Git.ver.of(h) == v : Git.Ver}
  for ne: {String.is_empty(r) == False{} : Bool}
  for ih: {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(r))) == False{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.step(v, h, r)))) == False{}
    : Bool}

def tail.step(h, r, n, v, ev, ne, ih):
  match v:
    case Git.No{}:
      ih
    case Git.Yes{+a, +b}:
      have.top(h, r, n, Git.Yes{a, b}, ev, String.is_empty(r), {==}, ne, ih)

def Laws.latest_greatest(xs, n, ys, ns, ps, ev):
  match xs:
    case []:
      head.step(n, Git.latest(ys), Git.ver.of(n), {==}, ns, ps, ev)
    case +h <> t:
      tail.step(h, Git.latest(List.append(&2, String, t, n <> ys)), n, Git.ver.of(h),
        {==}, latest.ne(t, n, ys, ns, ps, ev),
        Laws.latest_greatest(t, n, ys, ns, ps, ev))

# LAW: a release in the list makes the list have one
law has.hd:
  for +n: String
  for +ys: List<&2, String>
  for b: Bool
  for eb: {Git.release(n) == b : Bool}
  for er: {Git.release(n) == True{} : Bool}
  {Git.has.release.step(b, _u => Git.has.release(ys)) == True{} : Bool}

def has.hd(n, ys, b, eb, er):
  match b:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {Git.has.release.step(False{}, _u => Git.has.release(ys))
        == True{} : Bool},
        Equal.trans(Bool, False{}, Git.release(n), True{},
          Equal.sym(Bool, Git.release(n), False{}, eb), er))

# LAW: and a name in front of it does not take that away
law has.tl:
  for +t: List<&2, String>
  for b: Bool
  for ih: {Git.has.release(t) == True{} : Bool}
  {Git.has.release.step(b, _u => Git.has.release(t)) == True{} : Bool}

def has.tl(_t, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: a list with a release in it has one
law has.mem:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for er: {Git.release(n) == True{} : Bool}
  {Git.has.release(List.append(&2, String, xs, n <> ys)) == True{} : Bool}

def has.mem(xs, n, ys, er):
  match xs:
    case []:
      has.hd(n, ys, Git.release(n), {==}, er)
    case +h <> t:
      has.tl(List.append(&2, String, t, n <> ys), Git.release(h),
        has.mem(t, n, ys, er))

# LAW: the release fold's step at `n` holds nothing newer than `n`
law relh.step:
  for +n: String
  for +r: String
  for b: Bool
  for eb: {Git.release(n) == b : Bool}
  for er: {Git.release(n) == True{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.rel.step(b, n, r))))
    == False{} : Bool}

def relh.step(n, r, b, eb, er):
  match b:
    case True{}:
      head.have(n, r, Git.ver.of(n), {==}, String.is_empty(r))
    case False{}:
      Eq.bit.absurd(&2, {Git.newer(Git.ord.ver(Git.ver.of(n),
        Git.ver.of(Git.latest.rel.step(False{}, n, r)))) == False{} : Bool},
        Equal.trans(Bool, False{}, Git.release(n), True{},
          Equal.sym(Bool, Git.release(n), False{}, eb), er))

# LAW: a step of the release fold past `n` keeps `n` below
law relt.step:
  for +h: String
  for +r: String
  for +n: String
  for b: Bool
  for ne: {String.is_empty(r) == False{} : Bool}
  for ih: {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(r))) == False{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.latest.rel.step(b, h, r))))
    == False{} : Bool}

def relt.step(h, r, n, b, ne, ih):
  match b:
    case False{}:
      ih
    case True{}:
      have.top(h, r, n, Git.ver.of(h), {==}, String.is_empty(r), {==}, ne, ih)

def Laws.latest_rel_greatest(xs, n, ys, e):
  match xs:
    case []:
      relh.step(n, Git.latest.rel(ys), Git.release(n), {==}, e)
    case +h <> t:
      relt.step(h, Git.latest.rel(List.append(&2, String, t, n <> ys)), n,
        Git.release(h),
        rel_ne(List.append(&2, String, t, n <> ys), has.mem(t, n, ys, e)),
        Laws.latest_rel_greatest(t, n, ys, e))

# The choice is rewritten to the fold it takes: the release fold when the
# list has a release, and `latest` when it has none.
def Laws.choose_greatest_release(xs, n, ys, e):
  %Equal.sym(Bool,
    String.is_empty(Git.latest.rel(List.append(&2, String, xs, n <> ys))), False{},
    rel_ne(List.append(&2, String, xs, n <> ys), has.mem(xs, n, ys, e)))
    : {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(Git.choose.go(_,
      Git.latest.rel(List.append(&2, String, xs, n <> ys)),
      Git.latest(List.append(&2, String, xs, n <> ys)))))) == False{} : Bool}
  Laws.latest_rel_greatest(xs, n, ys, e)

def Laws.choose_greatest_prerelease(xs, n, ys, ns, ps, ev, e):
  %Equal.sym(String, Git.choose(List.append(&2, String, xs, n <> ys)),
    Git.latest(List.append(&2, String, xs, n <> ys)),
    Laws.choose_prerelease(List.append(&2, String, xs, n <> ys), e))
    : {Git.newer(Git.ord.ver(Git.ver.of(n), Git.ver.of(_))) == False{} : Bool}
  Laws.latest_greatest(xs, n, ys, ns, ps, ev)

# The chosen tag is one of the tags. `Mem(x, names)` is the shape
# `choose_is_a_tag` asks for: `names` split around `x`. Each fold answers the
# name in front, which splits there, or what it held from the rest, which
# splits one further along.

# `x` sits in `names`
def Mem(x: String, names: List<&2, String>) -> Type:
  &xs: List<&2, String> -> &ys: List<&2, String> ->
    {List.append(&2, String, xs, x <> ys) == names : List<&2, String>}

# LAW: the name in front is in the list
law mem.here:
  for +h: String
  for +t: List<&2, String>
  Mem(h, h <> t)

def mem.here(_h, t):
  ([], (t, {==}))

# LAW: a name in the rest is in the list
law mem.there:
  for +h: String
  for +t: List<&2, String>
  for +x: String
  for ih: Mem(x, t)
  Mem(x, h <> t)

def mem.there(h, t, x, ih):
  (xs, (ys, p)) = ih
  (h <> xs, (ys, Equal.cong(List<&2, String>, List<&2, String>, l => h <> l,
    List.append(&2, String, xs, x <> ys), t, p)))

# LAW: a name weighed against what the fold holds leaves one of the two
law mem.cmp:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for d: Bool
  for ec: {String.is_empty(r) == False{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(Git.latest.cmp(d, h, r), h <> t)

def mem.cmp(h, t, r, d, ec, ih):
  match d:
    case True{}:
      mem.here(h, t)
    case False{}:
      mem.there(h, t, r, ih(ec))

# LAW: and so does taking it when the fold holds nothing
law mem.have:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for +v: Git.Ver
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(Git.latest.have(c, h, r, v), h <> t)

def mem.have(h, t, r, v, c, ec, ih):
  match c:
    case True{}:
      mem.here(h, t)
    case False{}:
      mem.cmp(h, t, r, Git.newer(Git.ord.ver(v, Git.ver.of(r))), ec, ih)

# LAW: one step of `latest` answers a name in the list, when it answers one
law mem.step:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for +v: Git.Ver
  for e: {String.is_empty(Git.latest.step(v, h, r)) == False{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(Git.latest.step(v, h, r), h <> t)

def mem.step(h, t, r, v, e, ih):
  match v:
    case Git.No{}:
      mem.there(h, t, r, ih(e))
    case Git.Yes{+a, +b}:
      mem.have(h, t, r, Git.Yes{a, b}, String.is_empty(r), {==}, ih)

# LAW: `latest` answers a name in the list, when it answers one
law latest.mem:
  for +names: List<&2, String>
  for e: {String.is_empty(Git.latest(names)) == False{} : Bool}
  Mem(Git.latest(names), names)

def latest.mem(names, e):
  match names:
    case []:
      Eq.bit.absurd2(&1, Mem(Git.latest([]), []), e)
    case +h <> t:
      mem.step(h, t, Git.latest(t), Git.ver.of(h), e, x => latest.mem(t, x))

# LAW: one step of the release fold answers a name in the list
law mem.rel.step:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for b: Bool
  for e: {String.is_empty(Git.latest.rel.step(b, h, r)) == False{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(Git.latest.rel.step(b, h, r), h <> t)

def mem.rel.step(h, t, r, b, e, ih):
  match b:
    case False{}:
      mem.there(h, t, r, ih(e))
    case True{}:
      mem.have(h, t, r, Git.ver.of(h), String.is_empty(r), {==}, ih)

# LAW: the release fold answers a name in the list, when it answers one
law latest.rel.mem:
  for +names: List<&2, String>
  for e: {String.is_empty(Git.latest.rel(names)) == False{} : Bool}
  Mem(Git.latest.rel(names), names)

def latest.rel.mem(names, e):
  match names:
    case []:
      Eq.bit.absurd2(&1, Mem(Git.latest.rel([]), []), e)
    case +h <> t:
      mem.rel.step(h, t, Git.latest.rel(t), Git.release(h), e,
        x => latest.rel.mem(t, x))

# LAW: the choice answers a name in the list, from whichever fold it took
law mem.choose:
  for +names: List<&2, String>
  for c: Bool
  for ec: {String.is_empty(Git.latest.rel(names)) == c : Bool}
  for e: {String.is_empty(Git.choose.go(c, Git.latest.rel(names), Git.latest(names)))
    == False{} : Bool}
  Mem(Git.choose.go(c, Git.latest.rel(names), Git.latest(names)), names)

def mem.choose(names, c, ec, e):
  match c:
    case True{}:
      latest.mem(names, e)
    case False{}:
      latest.rel.mem(names, ec)

def Laws.choose_is_a_tag(names, e):
  mem.choose(names, String.is_empty(Git.latest.rel(names)), {==}, e)
