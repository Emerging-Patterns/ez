# proofs of laws/PublishNeedsCleanTree.bend
#
# The plan is `plan.v(decide(w), w)`: `decide` walks the stages a publish
# passes (the ledger, git status, the walk, what git tracks, the upload) and
# stops, waits or goes on at each; on `Go` the plan is `made(w)`, and every
# other verdict is a plan with no effect that refuses. Each stage reads what
# it needs from the World, so a law that one stage refuses walks `decide`
# stage by stage: every stage before it stops, waits, or goes on to the
# next, whatever the World says there.
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/add/world.bend as A
import ../src/add/hub.bend as H
import ../laws/PublishNeedsCleanTree.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

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
    case PP.Pending{asks}:
      Eq.bit.absurd(&2, {PP.sends.v(PP.Pending{asks}) == False{} : Bool}, r)
    case PP.Stop{_why}:
      {==}

def Laws.pub_stop_sends_nothing(w, r):
  stop_unsent(PP.decide(w), r)
