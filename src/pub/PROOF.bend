# pub: the proofs. `bend PROOF.bend` is the gate.
#
# The plan is `plan.v(decide(w), w)`: `decide` walks the stages a publish
# passes (the ledger, git status, the walk, what git tracks, the upload) and
# stops, waits or goes on at each; on `Go` the plan is `made(w)`, and every
# other verdict is a plan with no effect that refuses. Each stage reads what
# it needs from the World, so a law that one stage refuses walks `decide`
# stage by stage: every stage before it stops, waits, or goes on to the next,
# whatever the World says there.
import Base
import ./world.bend as PW
import ./plan.bend as PP
import ../lock/plan.bend as P
import ../pkg/pkg.bend as K
import ./blurb.bend as B
import ../git/git.bend as G
import ../check/eq.bend as Eq
import ../ledger/manifest.bend as M
import ../lock/lock.bend as L
import ./LAWS.bend as Laws

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
    G.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  {==}

def Laws.is_name_needs_length(s, e0, e1):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  %e1 : {Bool.and(_, G.hex.all(String.to_list(String.drop(s, 2n))))
    == False{} : Bool}
  {==}

def Laws.is_name_needs_hex(s, e0, e1, e2):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == False{} : Bool}
  %e1 : {Bool.and(_, G.hex.all(String.to_list(String.drop(s, 2n))))
    == False{} : Bool}
  %e2 : {_ == False{} : Bool}
  {==}

def Laws.is_name_hex34(s, e0, e1, e2):
  %e0 : {Bool.and(_, Bool.and(Nat.is_eq(String.length(s), PP.name.length()),
    G.hex.all(String.to_list(String.drop(s, 2n))))) == True{} : Bool}
  %e1 : {Bool.and(_, G.hex.all(String.to_list(String.drop(s, 2n))))
    == True{} : Bool}
  %e2 : {_ == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# the working tree and the package

# LAW: one line of the status against both walks at once. A line that says
# nothing hands each walk on to the rest of the status; a line that says
# something ends one walk at False and the other at True.
law clean_is_all_blank.arm:
  for t: List<&2, String>
  for q: Bool
  for ih: {PP.blanks(t) == Bool.not(PP.dirty.lines(t)) : Bool}
  {PP.blanks.step(q, _u => PP.blanks(t))
    == Bool.not(PP.dirty.step(q, _u => PP.dirty.lines(t))) : Bool}

def clean_is_all_blank.arm(_t, q, ih):
  match q:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.clean_is_all_blank(ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      clean_is_all_blank.arm(t, String.is_empty(h), Laws.clean_is_all_blank(t))

# A porcelain line that names a path opens with a character, so
# `String.is_empty` computes to False and the walk stops there. No status
# code is consulted, so none can be exempt.
def Laws.untracked_is_dirty(_path, _rest):
  {==}

def Laws.modified_is_dirty(_path, _rest):
  {==}

def Laws.staged_is_dirty(_path, _rest):
  {==}

# A tag other than `H` differs from `H` in its first character, so the
# comparison computes to False on the constructors and the walk goes on.
def Laws.assumed_is_untracked(_path, _rest):
  {==}

def Laws.skipped_is_untracked(_path, _rest):
  {==}

# ---------------------------------------------------------------------------
# a dirty tree, or no git: the command stops at git status

law dirty_led:
  for l: PP.Led
  for +w: PW.World
  for +text: String
  for e0: {PP.status(w) == PP.Said{text} : PP.Status}
  for e1: {PP.dirty(text) == True{} : Bool}
  {PP.stops.v(PP.decide.led(l, w)) == True{} : Bool}

def dirty_led(l, w, text, e0, e1):
  match l:
    case PP.Led{_e, _nv}:
      %Equal.sym(PP.Status, PP.status(w), PP.Said{text}, e0)
        : {PP.stops.v(PP.decide.status(_, w)) == True{} : Bool}
      %Equal.sym(Bool, PP.dirty(text), True{}, e1)
        : {PP.stops.v(PP.decide.clean(_, text, w)) == True{} : Bool}
      {==}
    case PP.LedNo{_why}:
      {==}

def Laws.pub_dirty_refuses(w, text, e0, e1):
  dirty_led(PP.led(w), w, text, e0, e1)

law gitless_led:
  for l: PP.Led
  for +w: PW.World
  for +why: String
  for e: {PP.status(w) == PP.StatusNo{why} : PP.Status}
  {PP.stops.v(PP.decide.led(l, w)) == True{} : Bool}

def gitless_led(l, w, why, e):
  match l:
    case PP.Led{_e, _nv}:
      %Equal.sym(PP.Status, PP.status(w), PP.StatusNo{why}, e)
        : {PP.stops.v(PP.decide.status(_, w)) == True{} : Bool}
      {==}
    case PP.LedNo{_why}:
      {==}

def Laws.pub_gitless_refuses(w, why, e):
  gitless_led(PP.led(w), w, why, e)

def Laws.pub_needs_ledger(_here, _rs):
  {==}

# ---------------------------------------------------------------------------
# a file git does not track: the command never reaches the upload

law stray_walk:
  for k: K.Walked
  for +w: PW.World
  for +path: String
  for e: {PP.stray(w) == PP.Stray{path} : PP.Kept}
  {PP.sends.v(PP.decide.walk(k, w)) == False{} : Bool}

def stray_walk(k, w, path, e):
  match k:
    case K.Walked{_h, _root, _fs, _sums}:
      %Equal.sym(PP.Kept, PP.stray(w), PP.Stray{path}, e)
        : {PP.sends.v(PP.decide.kept(_, w)) == False{} : Bool}
      {==}
    case K.Asks{_at}:
      {==}
    case K.Refused{_why}:
      {==}

law stray_clean:
  for b: Bool
  for +text: String
  for +w: PW.World
  for +path: String
  for e: {PP.stray(w) == PP.Stray{path} : PP.Kept}
  {PP.sends.v(PP.decide.clean(b, text, w)) == False{} : Bool}

def stray_clean(b, _text, w, path, e):
  match b:
    case True{}:
      {==}
    case False{}:
      stray_walk(PP.walked(w), w, path, e)

law stray_status:
  for s: PP.Status
  for +w: PW.World
  for +path: String
  for e: {PP.stray(w) == PP.Stray{path} : PP.Kept}
  {PP.sends.v(PP.decide.status(s, w)) == False{} : Bool}

def stray_status(s, w, path, e):
  match s:
    case PP.Said{+text}:
      stray_clean(PP.dirty(text), text, w, path, e)
    case PP.StatusWait{}:
      {==}
    case PP.StatusNo{_why}:
      {==}

law stray_led:
  for l: PP.Led
  for +w: PW.World
  for +path: String
  for e: {PP.stray(w) == PP.Stray{path} : PP.Kept}
  {PP.sends.v(PP.decide.led(l, w)) == False{} : Bool}

def stray_led(l, w, path, e):
  match l:
    case PP.Led{_e, _nv}:
      stray_status(PP.status(w), w, path, e)
    case PP.LedNo{_why}:
      {==}

def Laws.pub_stray_sends_nothing(w, path, e):
  stray_led(PP.led(w), w, path, e)

# ---------------------------------------------------------------------------
# a verdict that stops sends nothing, and one that sends nothing refuses

law stop_unsent:
  for v: PP.Verdict
  for r: {PP.stops.v(v) == True{} : Bool}
  {PP.sends.v(v) == False{} : Bool}

def stop_unsent(v, r):
  match v:
    case PP.Go{}:
      Eq.bit.absurd(&2, {PP.sends.v(PP.Go{}) == False{} : Bool}, r)
    case PP.Wait{asks}:
      Eq.bit.absurd(&2, {PP.sends.v(PP.Wait{asks}) == False{} : Bool}, r)
    case PP.Stop{_why}:
      {==}

def Laws.pub_stop_sends_nothing(w, r):
  stop_unsent(PP.decide(w), r)

law unsent_fails:
  for v: PP.Verdict
  for +w: PW.World
  for r: {PP.sends.v(v) == False{} : Bool}
  {PP.succeeds.plan(PP.plan.v(v, w)) == False{} : Bool}

def unsent_fails(v, w, r):
  match v:
    case PP.Go{}:
      Eq.bit.absurd2(&2, {PP.succeeds.plan(PP.plan.v(PP.Go{}, w)) == False{} : Bool}, r)
    case PP.Wait{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def Laws.pub_unsent_refuses(w, r):
  unsent_fails(PP.decide(w), w, r)

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

# ---------------------------------------------------------------------------
# what a publish that succeeds says, and that nothing is written

law said_made:
  for v: PP.Verdict
  for +w: PW.World
  for ok: {PP.succeeds.plan(PP.plan.v(v, w)) == True{} : Bool}
  {P.said(PP.plan.v(v, w)) == [PP.hash(w), G.import.line(PP.called(w), PP.at(w))]
    : List<&2, String>}

def said_made(v, w, ok):
  match v:
    case PP.Go{}:
      {==}
    case PP.Wait{asks}:
      Eq.bit.absurd(&2, {P.said(PP.plan.v(PP.Wait{asks}, w))
        == [PP.hash(w), G.import.line(PP.called(w), PP.at(w))] : List<&2, String>}, ok)
    case PP.Stop{why}:
      Eq.bit.absurd(&2, {P.said(PP.plan.v(PP.Stop{why}, w))
        == [PP.hash(w), G.import.line(PP.called(w), PP.at(w))] : List<&2, String>}, ok)

def Laws.pub_reports_ours(w, ok):
  said_made(PP.decide(w), w, ok)

law quiet:
  for v: PP.Verdict
  for +w: PW.World
  {P.writes(PP.plan.v(v, w)) == False{} : Bool}

def quiet(v, _w):
  match v:
    case PP.Go{}:
      {==}
    case PP.Wait{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def Laws.pub_refusal_writes_nothing(w, _r):
  quiet(PP.decide(w), w)

# ---------------------------------------------------------------------------
# EZ-OUT-1

# LAW: a plan ends with the status of whether it does not succeed
law plan_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(Bool.not(PP.succeeds.plan(pl))) : U32}

def plan_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.pub_exits_as_it_refuses(w):
  plan_code(PP.plan(w))

# ---------------------------------------------------------------------------
# the name a package is published under

# LAW: an `and` with False on its right is False
law and_false:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def and_false(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a character that is neither a digit nor a dot, after any stretch of a
# version, sinks the walk over its characters
law chars_sink:
  for +pre: String
  for +c: Char
  for +post: String
  for e: {False{} == PP.semver.char(c) : Bool}
  {PP.semver.chars(String.append(pre, SCon{c, post})) == False{} : Bool}

# by induction on the stretch: at its end the character answers False, and
# every character before it ands its own answer with that False
def chars_sink(pre, c, post, e):
  match pre:
    case SNil{}:
      %e : {Bool.and(_, PP.semver.chars(post)) == False{} : Bool}
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, PP.semver.chars(String.append(t, SCon{c, post})), False{},
        chars_sink(t, c, post, e))
        : {Bool.and(PP.semver.char(h), _) == False{} : Bool}
      and_false(PP.semver.char(h))

# The walk over the characters comes first in `semver`, so its False ends it.
def Laws.semver_needs_digits(pre, c, post, e):
  %Equal.sym(Bool, PP.semver.chars(String.append(pre, SCon{c, post})), False{},
    chars_sink(pre, c, post, e))
    : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, String,
        String.split(String.append(pre, SCon{c, post}), '.')), 3n),
        K.ver.nums(String.split(String.append(pre, SCon{c, post}), '.')))) == False{} : Bool}
  {==}

# `-` and `+` are neither digits nor dots, which computes.
def Laws.prerelease_refused(pre, post):
  Laws.semver_needs_digits(pre, '-', post, {==})

def Laws.build_refused(pre, post):
  Laws.semver_needs_digits(pre, '+', post, {==})

# Each emptiness test, and each check of a name and a version, is rewritten to
# the answer its premise gives, and `naming` computes to the arm it picks.
def Laws.neither_is_hash(pa, pv, e0, e1):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.ByHash{} : PP.Named}
  %e1 : {PP.naming.go(True{}, _, pa, pv) == PP.ByHash{} : PP.Named}
  {==}

def Laws.name_needs_version(pa, pv, e0, e1):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.nover(pa)}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.Unnamed{PP.why.nover(pa)} : PP.Named}
  {==}

def Laws.version_needs_name(pa, pv, e0, e1):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.noname(pv)}
    : PP.Named}
  %e1 : {PP.naming.go(True{}, _, pa, pv) == PP.Unnamed{PP.why.noname(pv)} : PP.Named}
  {==}

def Laws.bad_name_refused(pa, pv, e0, e1, en):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.name(pa)}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.Unnamed{PP.why.name(pa)} : PP.Named}
  %en : {PP.naming.both(_, PP.semver(pv), pa, pv) == PP.Unnamed{PP.why.name(pa)} : PP.Named}
  {==}

def Laws.bad_version_refused(pa, pv, e0, e1, en, ev):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.ver(pv)}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}
  %en : {PP.naming.both(_, PP.semver(pv), pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}
  %ev : {PP.naming.both(True{}, _, pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}
  {==}

def Laws.named_is_four_part(pa, pv, e0, e1, en, ev):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"} : PP.Named}
  %en : {PP.naming.both(_, PP.semver(pv), pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"}
    : PP.Named}
  %ev : {PP.naming.both(True{}, _, pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"} : PP.Named}
  {==}

def Laws.upload_by_hash(_entry):
  {==}

def Laws.upload_by_name(entry, nv, e):
  %e : {PP.upload.go(_, entry, nv) == ["bend", entry, "--publish", nv] : List<&2, String>}
  {==}

# ---------------------------------------------------------------------------
# the name, through the planner: the ledger's text is rewritten to the model
# it parses as, and the naming of its two keys to the answer the premise
# gives, and the stage computes

def Laws.pub_misnamed_stops(here, text, rs, n, e, b, h, pa, pv, ds, ts, why, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.stops.v(PP.decide.led(PP.led.read(_), PW.World{here, Some{text}, rs})) == True{} : Bool}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.Unnamed{why}, u)
    : {PP.stops.v(PP.decide.led(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _), PW.World{here,
      Some{text}, rs})) == True{} : Bool}
  {==}

def Laws.pub_misnamed_writes_nothing(here, text, rs, n, e, b, h, pa, pv, ds, ts, why, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.plan.v(PP.decide.led(PP.led.read(_), PW.World{here, Some{text}, rs}), PW.World{here, Some{text},
      rs}) == P.Plan{[], P.Refused{why}} : P.Plan}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.Unnamed{why}, u)
    : {PP.plan.v(PP.decide.led(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _), PW.World{here,
      Some{text}, rs}), PW.World{here, Some{text}, rs}) == P.Plan{[], P.Refused{why}} : P.Plan}
  {==}

def Laws.pub_named_uploads_named(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}),
      PP.named.word(PP.named.of(PP.led.read(_))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), nv, PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByName{nv}, u)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), PP.named.word(PP.named.of(PP.led.named(Bool.pick(String,
      String.is_empty(e), "main.bend", e), _))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), nv, PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  {==}

def Laws.pub_unnamed_uploads_by_hash(here, text, rs, n, e, b, h, pa, pv, ds, ts, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}),
      PP.named.word(PP.named.of(PP.led.read(_))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), "", PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByHash{}, u)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), PP.named.word(PP.named.of(PP.led.named(Bool.pick(String,
      String.is_empty(e), "main.bend", e), _))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), "", PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  {==}

# LAW: a World whose ledger names the package calls it by that name
law called_named:
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
  for +ts: List<&2, M.Tool>
  for +nv: String
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.ByName{nv} : PP.Named}
  {PP.called(PW.World{here, Some{text}, rs}) == nv : String}

def called_named(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.called.of(PP.named.of(PP.led.read(_)), PP.hash(PW.World{here, Some{text}, rs})) == nv : String}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByName{nv}, u)
    : {PP.called.of(PP.named.of(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _)),
      PP.hash(PW.World{here, Some{text}, rs})) == nv : String}
  {==}

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
  for +ts: List<&2, M.Tool>
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

# What a publish that succeeds says (`pub_reports_ours`), with what it calls
# the package rewritten to the name or the hash.
def Laws.pub_reports_name(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g, u, ok):
  Equal.trans(List<&2, String>, P.said(PP.plan(PW.World{here, Some{text}, rs})),
    [PP.hash(PW.World{here, Some{text}, rs}), G.import.line(PP.called(PW.World{here, Some{text}, rs}),
      PP.at(PW.World{here, Some{text}, rs}))],
    [PP.hash(PW.World{here, Some{text}, rs}), G.import.line(nv, PP.at(PW.World{here, Some{text}, rs}))],
    Laws.pub_reports_ours(PW.World{here, Some{text}, rs}, ok),
    Equal.cong(String, List<&2, String>,
      x => [PP.hash(PW.World{here, Some{text}, rs}), G.import.line(x, PP.at(PW.World{here, Some{text}, rs}))],
      PP.called(PW.World{here, Some{text}, rs}), nv, called_named(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g,
        u)))

def Laws.pub_reports_hash(here, text, rs, n, e, b, h, pa, pv, ds, ts, g, u, ok):
  Equal.trans(List<&2, String>, P.said(PP.plan(PW.World{here, Some{text}, rs})),
    [PP.hash(PW.World{here, Some{text}, rs}), G.import.line(PP.called(PW.World{here, Some{text}, rs}),
      PP.at(PW.World{here, Some{text}, rs}))],
    [PP.hash(PW.World{here, Some{text}, rs}), G.import.line(PP.hash(PW.World{here, Some{text}, rs}),
      PP.at(PW.World{here, Some{text}, rs}))],
    Laws.pub_reports_ours(PW.World{here, Some{text}, rs}, ok),
    Equal.cong(String, List<&2, String>,
      x => [PP.hash(PW.World{here, Some{text}, rs}), G.import.line(x, PP.at(PW.World{here, Some{text}, rs}))],
      PP.called(PW.World{here, Some{text}, rs}), PP.hash(PW.World{here, Some{text}, rs}), called_hash(here, text, rs,
        n, e, b, h, pa, pv, ds, ts, g, u)))

# ---------------------------------------------------------------------------
# the hub description

# LAW: one character of the line: a newline contradicts the premise, and any
# other character is the line's own, with the rest of the line after it
law line_first_cut.arm:
  for +h: Char
  for t: String
  for +b: String
  for c: Bool
  for one: {B.nl.step(c, _u => B.has.nl(t)) == False{} : Bool}
  for ih: {B.has.nl(t) == False{} : Bool} -> {B.line.first(t ++ "\n" ++ b) == t : String}
  {B.line.step(c, h, _u => B.line.first(t ++ "\n" ++ b)) == SCon{h, t} : String}

def line_first_cut.arm(h, t, b, c, one, ih):
  match c:
    case True{}:
      Eq.bit.absurd2(&2, {B.line.step(True{}, h, _u => B.line.first(t ++ "\n" ++ b)) == SCon{h, t} : String}, one)
    case False{}:
      Equal.cong(String, String, x => SCon{h, x}, B.line.first(t ++ "\n" ++ b), t, ih(one))

def Laws.line_first_cut(a, b, one):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      line_first_cut.arm(h, t, b, Char.is_eq(h, '\n'), one, x => Laws.line_first_cut(t, b, x))

def Laws.hub_license_named(_t):
  {==}

# A LICENSE is passed over by the first step of the scan.
def Laws.hub_skips_license(p, t, fs, l):
  %Equal.sym(Bool, B.lic(K.Source{p, t}), True{}, l)
    : {B.line.of(B.least(fs, B.least.pick(_, None{}, K.Source{p, t}))) == B.blurb(fs) : String}
  {==}

# LAW: a file found first whose path comes no later than any file after it
# is the one the scan ends with
law keeps_least:
  for fs: List<&2, K.Source>
  for +p: String
  for +t: String
  for af: {B.after(p, fs) == True{} : Bool}
  {B.least(fs, Some{K.Source{p, t}}) == Some{K.Source{p, t}} : Maybe<&2, K.Source>}

# LAW: one file of the scan, with whether its path comes no earlier and
# whether it is a LICENSE in hand
law keeps_least.arm:
  for +h: K.Source
  for r: List<&2, K.Source>
  for +p: String
  for +t: String
  for b: Bool
  for eb: {String.is_le(p, B.at(h)) == b : Bool}
  for k: Bool
  for af: {B.after.step(b, _u => B.after(p, r)) == True{} : Bool}
  for ih: {B.after(p, r) == True{} : Bool}
    -> {B.least(r, Some{K.Source{p, t}}) == Some{K.Source{p, t}} : Maybe<&2, K.Source>}
  {B.least(r, B.least.pick(k, Some{K.Source{p, t}}, h)) == Some{K.Source{p, t}} : Maybe<&2, K.Source>}

def keeps_least.arm(h, r, p, t, b, eb, k, af, ih):
  match b:
    case False{}:
      Eq.bit.absurd(&2, {B.least(r, B.least.pick(k, Some{K.Source{p, t}}, h)) == Some{K.Source{p, t}}
        : Maybe<&2, K.Source>}, af)
    case True{}:
      match k:
        case True{}:
          ih(af)
        case False{}:
          %Equal.sym(Bool, String.is_le(p, B.at(h)), True{}, eb)
            : {B.least(r, Bool.pick(Maybe<&2, K.Source>, _, Some{K.Source{p, t}}, Some{h}))
              == Some{K.Source{p, t}} : Maybe<&2, K.Source>}
          ih(af)

def keeps_least(fs, p, t, af):
  match fs:
    case []:
      {==}
    case +h <> +r:
      keeps_least.arm(h, r, p, t, String.is_le(p, B.at(h)), {==}, B.lic(h), af, x => keeps_least(r, p, t, x))

# A file that is not a LICENSE starts the scan, and nothing after it comes
# earlier.
def Laws.hub_first_by_path(p, t, fs, nl, af):
  %Equal.sym(Bool, B.lic(K.Source{p, t}), False{}, nl)
    : {B.line.of(B.least(fs, B.least.pick(_, None{}, K.Source{p, t}))) == B.line.first(t) : String}
  Equal.cong(Maybe<&2, K.Source>, String, m => B.line.of(m), B.least(fs, Some{K.Source{p, t}}),
    Some{K.Source{p, t}}, keeps_least(fs, p, t, af))

def Laws.pub_upload_says_description(_w):
  {==}

# ---------------------------------------------------------------------------
# the hub packages the package imports: the upload is reached only past a
# World in which every one of them is on the hub

# LAW: the questions about the hub are none of them the upload
law asks_quiet:
  for +hub: String
  for ps: List<&2, PP.Probe>
  {PP.any.upload(PP.probe.asks(hub, ps)) == False{} : Bool}

def asks_quiet(hub, ps):
  match ps:
    case []:
      {==}
    case _h <> t:
      asks_quiet(hub, t)

# LAW: the hub stage gets as far as the upload only when every hub import is
# on the hub. Still asking is asking the hub, not bend, and off the hub stops.
law on_hub:
  for h: PP.Hubbed
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.hub(h, w)) == True{} : Bool}
  {PP.on.hub.v(h) == True{} : Bool}

def on_hub(h, w, s):
  match h:
    case PP.OnHub{}:
      {==}
    case PP.HubWait{open}:
      Eq.bit.absurd(&2, {PP.on.hub.v(PP.HubWait{open}) == True{} : Bool},
        Equal.trans(Bool, False{}, PP.any.upload(PP.probe.asks(PP.hub(w), open)), True{},
          Equal.sym(Bool, PP.any.upload(PP.probe.asks(PP.hub(w), open)), False{},
            asks_quiet(PP.hub(w), open)),
          s))
    case PP.OffHub{why}:
      Eq.bit.absurd(&2, {PP.on.hub.v(PP.OffHub{why}) == True{} : Bool}, s)

law hub_lock.got:
  for got: PW.Heard
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.lock(True{}, got, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_lock.got(got, w, s):
  match got:
    case PW.Open{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PW.Heard{_a}:
      on_hub(PP.hubbed(w), w, s)

law hub_lock:
  for need: Bool
  for got: PW.Heard
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.lock(need, got, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_lock(need, got, w, s):
  match need:
    case False{}:
      on_hub(PP.hubbed(w), w, s)
    case True{}:
      hub_lock.got(got, w, s)

law hub_kept:
  for k: PP.Kept
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.kept(k, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_kept(k, w, s):
  match k:
    case PP.Kept{}:
      hub_lock(PP.any(PP.nvs(w)), PW.heard(w, PW.Lock{}), w, s)
    case PP.Stray{_path}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PP.KeptWait{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PP.KeptNo{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

law hub_walk:
  for k: K.Walked
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.walk(k, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_walk(k, w, s):
  match k:
    case K.Walked{_h, _root, _fs, _sums}:
      hub_kept(PP.stray(w), w, s)
    case K.Asks{_at}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case K.Refused{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

law hub_clean:
  for b: Bool
  for +text: String
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.clean(b, text, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_clean(b, _text, w, s):
  match b:
    case True{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case False{}:
      hub_walk(PP.walked(w), w, s)

law hub_status:
  for st: PP.Status
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.status(st, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_status(st, w, s):
  match st:
    case PP.Said{+text}:
      hub_clean(PP.dirty(text), text, w, s)
    case PP.StatusWait{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PP.StatusNo{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

law hub_led:
  for l: PP.Led
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.led(l, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_led(l, w, s):
  match l:
    case PP.Led{_e, _nv}:
      hub_status(PP.status(w), w, s)
    case PP.LedNo{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

def Laws.pub_sends_only_on_hub(w, s):
  hub_led(PP.led(w), w, s)

# LAW: a bit that is True only when every hub import is on the hub is False
# when one is not
law off_flip:
  for b: Bool
  for +w: PW.World
  for f: {b == True{} : Bool} -> {PP.on.hub(w) == True{} : Bool}
  for e: {PP.on.hub(w) == False{} : Bool}
  {b == False{} : Bool}

def off_flip(b, w, f, e):
  match b:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.trans(Bool, False{}, PP.on.hub(w), True{},
          Equal.sym(Bool, PP.on.hub(w), False{}, e), f({==})))
    case False{}:
      {==}

def Laws.pub_offhub_sends_nothing(w, why, e):
  off_flip(PP.sends(w), w, x => Laws.pub_sends_only_on_hub(w, x),
    Equal.cong(PP.Hubbed, Bool, x => PP.on.hub.v(x), PP.hubbed(w), PP.OffHub{why}, e))

def Laws.pub_offhub_refuses(w, why, e):
  Laws.pub_unsent_refuses(w, Laws.pub_offhub_sends_nothing(w, why, e))

# LAW: a verdict that sends nothing has a plan with no effect
law unsent_quiet:
  for v: PP.Verdict
  for +w: PW.World
  for r: {PP.sends.v(v) == False{} : Bool}
  {P.effects(PP.plan.v(v, w)) == [] : List<&2, P.Effect>}

def unsent_quiet(v, w, r):
  match v:
    case PP.Go{}:
      Eq.bit.absurd2(&2, {P.effects(PP.plan.v(PP.Go{}, w)) == [] : List<&2, P.Effect>}, r)
    case PP.Wait{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def Laws.pub_offhub_writes_nothing(w, why, e):
  unsent_quiet(PP.decide(w), w, Laws.pub_offhub_sends_nothing(w, why, e))

# LAW: a probe still to ask about keeps the hub stage waiting
law ask_head:
  for p: PP.Probe
  for t: PP.Tally
  for +hub: String
  {PP.on.hub.v(PP.hubbed.of(PP.tally.unasked(p, t), hub)) == False{} : Bool}

def ask_head(_p, t, _hub):
  match t:
    case PP.Tally{_open, _offs}:
      {==}

# LAW: a line off the hub makes the tally off the hub, asked or not
law off_head.go:
  for open: List<&2, PP.Probe>
  for offs: List<&2, String>
  for +hub: String
  for +line: String
  {PP.on.hub.v(PP.hubbed.go(open, line <> offs, hub)) == False{} : Bool}

def off_head.go(open, _offs, _hub, _line):
  match open:
    case []:
      {==}
    case _h <> _t:
      {==}

law off_head:
  for t: PP.Tally
  for +hub: String
  for +line: String
  {PP.on.hub.v(PP.hubbed.of(PP.tally.offhub(line, t), hub)) == False{} : Bool}

def off_head(t, hub, line):
  match t:
    case PP.Tally{open, offs}:
      off_head.go(open, offs, hub, line)

# LAW: a tally that is not on the hub stays so, whatever is added to it
law off_put:
  for s: PP.Seen
  for p: PP.Probe
  for t: PP.Tally
  for +hub: String
  for ih: {PP.on.hub.v(PP.hubbed.of(t, hub)) == False{} : Bool}
  {PP.on.hub.v(PP.hubbed.of(PP.tally.put(s, p, t), hub)) == False{} : Bool}

def off_put(s, p, t, hub, ih):
  match s:
    case PP.There{}:
      ih
    case PP.Unasked{}:
      ask_head(p, t, hub)
    case PP.Off{line}:
      off_head(t, hub, line)

def Laws.hub_one_off_is_off(w, hub, ds, pre, p, post, line, e):
  match pre:
    case []:
      %Equal.sym(PP.Seen, PP.seen(w, hub, ds, p), PP.Off{line}, e)
        : {PP.on.hub.v(PP.hubbed.of(PP.tally.put(_, p, PP.tally(w, hub, ds, post)), hub))
          == False{} : Bool}
      off_head(PP.tally(w, hub, ds, post), hub, line)
    case +h <> +t:
      off_put(PP.seen(w, hub, ds, h), h,
        PP.tally(w, hub, ds, List.append(&2, PP.Probe, t, p <> post)), hub,
        Laws.hub_one_off_is_off(w, hub, ds, t, p, post, line, e))

def Laws.hub_404_is_absent(p, _who):
  match p:
    case PP.ProbeHash{_h}:
      {==}
    case PP.ProbeName{_nv, _h}:
      {==}

def Laws.hub_unreachable_is_off(p, text, who, e):
  match p:
    case PP.ProbeHash{_h}:
      %Equal.sym(Bool, PP.absent(text), False{}, e)
        : {PP.seen.miss(_, text, who) == PP.Off{PP.why.unasked(who, text)} : PP.Seen}
      {==}
    case PP.ProbeName{_nv, _h}:
      %Equal.sym(Bool, PP.absent(text), False{}, e)
        : {PP.seen.miss(_, text, who) == PP.Off{PP.why.unasked(who, text)} : PP.Seen}
      {==}

def Laws.hub_name_elsewhere_is_off(got, want, who, e0, e1):
  %Equal.sym(Bool, String.eq(got, want), False{}, e0)
    : {PP.seen.named.go(Bool.and(Bool.or(_, String.is_empty(want)), L.hash.ok(got)),
      got, want, who) == PP.Off{PP.why.named(got, want, who)} : PP.Seen}
  %Equal.sym(Bool, String.is_empty(want), False{}, e1)
    : {PP.seen.named.go(Bool.and(Bool.or(False{}, _), L.hash.ok(got)),
      got, want, who) == PP.Off{PP.why.named(got, want, who)} : PP.Seen}
  {==}

def Laws.hub_name_there(got, want, who, e0, e1):
  %Equal.sym(Bool, String.eq(got, want), True{}, e0)
    : {PP.seen.named.go(Bool.and(Bool.or(_, String.is_empty(want)), L.hash.ok(got)),
      got, want, who) == PP.There{} : PP.Seen}
  %Equal.sym(Bool, L.hash.ok(got), True{}, e1)
    : {PP.seen.named.go(Bool.and(Bool.or(True{}, String.is_empty(want)), _),
      got, want, who) == PP.There{} : PP.Seen}
  {==}
