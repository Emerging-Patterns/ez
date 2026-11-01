# proofs of laws/PublishNeedsDepsOnHub.bend
import Base
import ../src/pub/plan.bend as PP
import ../src/lock/lock.bend as L
import ../laws/PublishNeedsCleanTree.bend as L1
import ../laws/PublishNeedsDepsOnHub.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

def Laws.pub_offhub_refuses(w, why, e):
  L1.pub_unsent_refuses(w, Laws.pub_offhub_sends_nothing(w, why, e))

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
