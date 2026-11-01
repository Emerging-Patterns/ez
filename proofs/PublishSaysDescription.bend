# proofs of laws/PublishSaysDescription.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/pub/blurb.bend as B
import ../src/add/world.bend as A
import ../laws/PublishSaysDescription.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

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
