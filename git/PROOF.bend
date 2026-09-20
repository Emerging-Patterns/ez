# git: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../manifest/toml.bend as T
import ../lock/lock.bend as L
import ../git/git.bend as G
import ./LAWS.bend as Laws

# The six keys are written out as literals on both sides, so every lookup in
# `L.src_of` decides against a literal and computes: `kind` finds "git", each
# named key finds the pair written for it, and `tag` runs off the end of the
# six into whatever follows. Nothing is left symbolic but the values, and they
# are carried through untouched.
def Laws.origin_read(_url, _rev, _entry, _root, _nar, _ts):
  {==}

# The three agreement laws at the foot of LAWS.bend, which say that this
# pass's rewrites for cost did not change an answer. Each is the same
# argument: a `match` may not scrutinise a computed value, so the head's
# answer is lifted into a parameter and the law is then applied to the answer
# the code computes.

# LAW: one step of the alphabet scan
law among_agrees.arm:
  for +c: Char
  for t: List<&2, Char>
  for p: Bool
  for ih: {Laws.old.among(c, t) == G.among(c, t) : Bool}
  {Bool.or(p, Laws.old.among(c, t))
    == G.among.step(p, _u => G.among(c, t)) : Bool}

def among_agrees.arm(_c, _t, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.among_agrees(c, cs):
  match cs:
    case []:
      {==}
    case +h <> +t:
      among_agrees.arm(c, t, Char.is_eq(h, c), Laws.among_agrees(c, t))

# LAW: one step of the ref walk
law hex_all_agrees.arm:
  for t: List<&2, Char>
  for p: Bool
  for ih: {Laws.old.hex.all(t) == G.hex.all(t) : Bool}
  {Bool.and(p, Laws.old.hex.all(t))
    == G.hex.all.step(p, _u => G.hex.all(t)) : Bool}

def hex_all_agrees.arm(_t, p, ih):
  match p:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.hex_all_agrees(cs):
  match cs:
    case []:
      {==}
    case +h <> +t:
      hex_all_agrees.arm(t, G.hex.at(h), Laws.hex_all_agrees(t))

# LAW: one step of the peeled-row search
law peeled_agrees.arm:
  for +h: G.Row
  for t: List<&2, G.Row>
  for p: Bool
  for ih: {Laws.old.peeled(t) == G.peeled(t) : String}
  {Bool.pick(String, p, G.row.rev(h), Laws.old.peeled(t))
    == G.peeled.step(p, G.row.rev(h), _u => G.peeled(t)) : String}

def peeled_agrees.arm(_h, _t, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.peeled_agrees(rs):
  match rs:
    case []:
      {==}
    case +h <> +t:
      peeled_agrees.arm(h, t, G.row.peeled(h), Laws.peeled_agrees(t))
