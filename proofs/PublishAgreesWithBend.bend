# proofs of laws/PublishAgreesWithBend.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/git/git.bend as Git
import ../src/add/world.bend as A
import ../laws/PublishAgreesWithBend.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1

# ---------------------------------------------------------------------------
# bend's answer

# LAW: past a stretch with no name in it, the check answers what it had seen
law agrees_skip:
  for +ours: String
  for ls: List<&2, String>
  for +s: Bool
  for e: {False{} == Laws.any_name(ls) : Bool}
  {PP.agrees.go(ours, ls, s) == s : Bool}

# LAW: one line of that stretch. A line that is a name contradicts the
# premise; one that is not hands the goal on unchanged.
law agrees_skip.arm:
  for +ours: String
  for +h: String
  for t: List<&2, String>
  for +s: Bool
  for p: Bool
  for e: {False{} == Laws.any_name.step(p, _u => Laws.any_name(t)) : Bool}
  for ih: {False{} == Laws.any_name(t) : Bool} -> {PP.agrees.go(ours, t, s) == s : Bool}
  {PP.agrees.step(p, String.eq(ours, h), s, x => PP.agrees.go(ours, t, x)) == s : Bool}

def agrees_skip.arm(_ours, _h, _t, s, p, e, ih):
  match p:
    case True{}:
      Eq.bit.absurd(&2, {PP.agrees.step(True{}, String.eq(_ours, _h), s,
        x => PP.agrees.go(_ours, _t, x)) == s : Bool}, e)
    case False{}:
      ih(e)

def agrees_skip(ours, ls, s, e):
  match ls:
    case []:
      {==}
    case +h <> +t:
      agrees_skip.arm(ours, h, t, s, PP.is_name(h), e, x => agrees_skip(ours, t, s, x))

def Laws.unread_never_agrees(ours, ls, e):
  agrees_skip(ours, ls, False{}, e)

# LAW: past a stretch with no name in it, the check goes on as if it began
# after it
law skip_prefix:
  for +ours: String
  for pre: List<&2, String>
  for +rest: List<&2, String>
  for +s: Bool
  for e: {False{} == Laws.any_name(pre) : Bool}
  {PP.agrees.go(ours, List.append(&2, String, pre, rest), s) == PP.agrees.go(ours, rest, s)
    : Bool}

law skip_prefix.arm:
  for +ours: String
  for +h: String
  for t: List<&2, String>
  for +rest: List<&2, String>
  for +s: Bool
  for p: Bool
  for e: {False{} == Laws.any_name.step(p, _u => Laws.any_name(t)) : Bool}
  for ih: {False{} == Laws.any_name(t) : Bool} ->
    {PP.agrees.go(ours, List.append(&2, String, t, rest), s) == PP.agrees.go(ours, rest, s)
      : Bool}
  {PP.agrees.step(p, String.eq(ours, h), s,
    x => PP.agrees.go(ours, List.append(&2, String, t, rest), x))
    == PP.agrees.go(ours, rest, s) : Bool}

def skip_prefix.arm(ours, h, t, rest, s, p, e, ih):
  match p:
    case True{}:
      Eq.bit.absurd(&2, {PP.agrees.step(True{}, String.eq(ours, h), s,
        x => PP.agrees.go(ours, List.append(&2, String, t, rest), x))
        == PP.agrees.go(ours, rest, s) : Bool}, e)
    case False{}:
      ih(e)

def skip_prefix(ours, pre, rest, s, e):
  match pre:
    case []:
      {==}
    case +h <> +t:
      skip_prefix.arm(ours, h, t, rest, s, PP.is_name(h), e,
        x => skip_prefix(ours, t, rest, s, x))

# LAW: a name that is not ours, wherever it is, sinks the check whatever it
# had seen before
law differs_go:
  for +ours: String
  for pre: List<&2, String>
  for +h: String
  for +post: List<&2, String>
  for +s: Bool
  for +e0: {True{} == PP.is_name(h) : Bool}
  for +e1: {False{} == String.eq(ours, h) : Bool}
  {PP.agrees.go(ours, List.append(&2, String, pre, h <> post), s) == False{} : Bool}

# LAW: one line before that name. A name ands its own verdict with the
# rest's, which is False; any other line hands the rest on.
law differs_go.arm:
  for p: Bool
  for q: Bool
  for +s: Bool
  for f: Bool -> Bool
  for yes: {f(True{}) == False{} : Bool}
  for no: {f(s) == False{} : Bool}
  {PP.agrees.step(p, q, s, f) == False{} : Bool}

def differs_go.arm(p, q, _s, _f, yes, no):
  match p:
    case True{}:
      match q:
        case True{}:
          yes
        case False{}:
          {==}
    case False{}:
      no

def differs_go(ours, pre, h, post, s, e0, e1):
  match pre:
    case []:
      %e0 : {PP.agrees.step(_, String.eq(ours, h), s,
        x => PP.agrees.go(ours, post, x)) == False{} : Bool}
      %e1 : {PP.agrees.step(True{}, _, s,
        x => PP.agrees.go(ours, post, x)) == False{} : Bool}
      {==}
    case +x <> +t:
      differs_go.arm(PP.is_name(x), String.eq(ours, x), s,
        y => PP.agrees.go(ours, List.append(&2, String, t, h <> post), y),
        differs_go(ours, t, h, post, True{}, e0, e1),
        differs_go(ours, t, h, post, s, e0, e1))

def Laws.differs_never_agrees(ours, pre, h, post, e0, e1):
  differs_go(ours, pre, h, post, False{}, e0, e1)

# The name that is ours, once the stretch before it is passed over, is a
# name seen, and the stretch after it has no name to spoil it.
law ours_at:
  for +ours: String
  for +h: String
  for +post: List<&2, String>
  for e0: {True{} == PP.is_name(h) : Bool}
  for e1: {True{} == String.eq(ours, h) : Bool}
  for e3: {False{} == Laws.any_name(post) : Bool}
  {PP.agrees.go(ours, h <> post, False{}) == True{} : Bool}

def ours_at(ours, h, post, e0, e1, e3):
  %e0 : {PP.agrees.step(_, String.eq(ours, h), False{},
    x => PP.agrees.go(ours, post, x)) == True{} : Bool}
  %e1 : {PP.agrees.step(True{}, _, False{},
    x => PP.agrees.go(ours, post, x)) == True{} : Bool}
  agrees_skip(ours, post, True{}, e3)

def Laws.ours_agrees(ours, pre, h, post, e0, e1, e2, e3):
  Equal.trans(Bool,
    PP.agrees.go(ours, List.append(&2, String, pre, h <> post), False{}),
    PP.agrees.go(ours, h <> post, False{}), True{},
    skip_prefix(ours, pre, h <> post, False{}, e2),
    ours_at(ours, h, post, e0, e1, e3))

# Both decoy lines are refused on their first character: `is_name` opens with
# `String.starts_with(s, "0x")`, the literal prefix is a known constructor and
# so is the head of each literal, so the comparison computes to False before
# the length or the alphabet is reached.
def Laws.progress_is_not_an_answer(_rest):
  {==}

def Laws.import_is_not_an_answer(_rest):
  {==}

# A name's prefix, length or alphabet is rewritten into `Bool.and`.
def Laws.is_name_needs_0x(s, e):
  %e : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    Git.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  {==}

def Laws.is_name_needs_length(s, e0, e1):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    Git.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  %e1 : {Bool.and(_, Git.hex.all(String.to_list(String.drop(s, 2n))))
    == False{} : Bool}
  {==}

def Laws.is_name_needs_hex(s, e0, e1, e2):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    Git.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  %e1 : {Bool.and(_, Git.hex.all(String.to_list(String.drop(s, 2n))))
    == False{} : Bool}
  %e2 : {_ == False{} : Bool}
  {==}

def Laws.is_name_hex34(s, e0, e1, e2):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    Git.hex.all(String.to_list(String.drop(s, 2n))))) == True{} : Bool}
  %e1 : {Bool.and(_, Git.hex.all(String.to_list(String.drop(s, 2n))))
    == True{} : Bool}
  %e2 : {_ == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# an upload that does not agree: the command does not succeed

law ag_upload:
  for got: PW.Heard
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.upload(got, w), w)) == False{} : Bool}

def ag_upload(got, w, e):
  match got:
    case PW.Open{}:
      {==}
    case PW.Heard{_a}:
      %Equal.sym(Bool, PP.agreed(w), False{}, e)
        : {PP.succeeds.plan(PP.plan.v(PP.decide.agreed(_, w), w)) == False{} : Bool}
      {==}

law ag_hub:
  for h: PP.Hubbed
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.hub(h, w), w)) == False{} : Bool}

def ag_hub(h, w, e):
  match h:
    case PP.OnHub{}:
      ag_upload(PP.uploaded(w), w, e)
    case PP.HubWait{_open}:
      {==}
    case PP.OffHub{_why}:
      {==}

law ag_lock.got:
  for got: PW.Heard
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.lock(True{}, got, w), w)) == False{} : Bool}

def ag_lock.got(got, w, e):
  match got:
    case PW.Open{}:
      {==}
    case PW.Heard{_a}:
      ag_hub(PP.hubbed(w), w, e)

law ag_lock:
  for need: Bool
  for got: PW.Heard
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.lock(need, got, w), w)) == False{} : Bool}

def ag_lock(need, got, w, e):
  match need:
    case False{}:
      ag_hub(PP.hubbed(w), w, e)
    case True{}:
      ag_lock.got(got, w, e)

law ag_kept:
  for k: PP.Kept
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.kept(k, w), w)) == False{} : Bool}

def ag_kept(k, w, e):
  match k:
    case PP.Kept{}:
      ag_lock(PP.any(PP.nvs(w)), PW.heard(w, PW.Lock{}), w, e)
    case PP.Stray{_path}:
      {==}
    case PP.KeptWait{}:
      {==}
    case PP.KeptNo{_why}:
      {==}

law ag_walk:
  for k: K.Walked
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.walk(k, w), w)) == False{} : Bool}

def ag_walk(k, w, e):
  match k:
    case K.Walked{_h, _root, _fs, _sums}:
      ag_kept(PP.stray(w), w, e)
    case K.Asks{_at}:
      {==}
    case K.Refused{_why}:
      {==}

law ag_clean:
  for b: Bool
  for +text: String
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.clean(b, text, w), w)) == False{} : Bool}

def ag_clean(b, _text, w, e):
  match b:
    case True{}:
      {==}
    case False{}:
      ag_walk(PP.walked(w), w, e)

law ag_status:
  for s: PP.Status
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.status(s, w), w)) == False{} : Bool}

def ag_status(s, w, e):
  match s:
    case PP.Said{+text}:
      ag_clean(PP.dirty(text), text, w, e)
    case PP.StatusWait{}:
      {==}
    case PP.StatusNo{_why}:
      {==}

law ag_led:
  for l: PP.Led
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(PP.decide.led(l, w), w)) == False{} : Bool}

def ag_led(l, w, e):
  match l:
    case PP.Led{_e, _nv}:
      ag_status(PP.status(w), w, e)
    case PP.LedNo{_why}:
      {==}

def Laws.pub_needs_agreement(w, e):
  ag_led(PP.led(w), w, e)

# LAW: and one whose ledger names none calls it by its hash
law called_hash:
  for +here: String
  for +text: String
  for +rs: List<&2, PW.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +pa: String
  for +pv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.ByHash{} : PP.Named}
  {PP.called(PW.World{here, Some{text}, rs}) == PP.hash(PW.World{here, Some{text}, rs}) : String}

def called_hash(here, text, rs, n, e, b, h, pa, pv, ds, ts, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.called.of(PP.named.of(PP.led.read(_)), PP.hash(PW.World{here, Some{text}, rs})) == PP.hash(PW.World{here,
      Some{text}, rs}) : String}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByHash{}, u)
    : {PP.called.of(PP.named.of(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _)),
      PP.hash(PW.World{here, Some{text}, rs})) == PP.hash(PW.World{here, Some{text}, rs}) : String}
  {==}

def Laws.pub_reports_hash(here, text, rs, n, e, b, h, pa, pv, ds, ts, g, u, ok):
  Equal.trans(List<&2, String>, P.said(PP.plan(PW.World{here, Some{text}, rs})),
    [PP.hash(PW.World{here, Some{text}, rs}), Git.import.line(PP.called(PW.World{here, Some{text}, rs}),
      PP.at(PW.World{here, Some{text}, rs}))],
    [PP.hash(PW.World{here, Some{text}, rs}), Git.import.line(PP.hash(PW.World{here, Some{text}, rs}),
      PP.at(PW.World{here, Some{text}, rs}))],
    Laws.pub_reports_ours(PW.World{here, Some{text}, rs}, ok),
    Equal.cong(String, List<&2, String>,
      x => [PP.hash(PW.World{here, Some{text}, rs}), Git.import.line(x, PP.at(PW.World{here, Some{text}, rs}))],
      PP.called(PW.World{here, Some{text}, rs}), PP.hash(PW.World{here, Some{text}, rs}), called_hash(here, text, rs,
        n, e, b, h, pa, pv, ds, ts, g, u)))
