# `ez lock` output is a function of the ledger and the committed tree. A fresh
# clone reproduces the lock byte for byte.
#
# This guarantee reads the committed tree as bend reads it. A hub import
# line is a root of the lock whatever run of spaces and tabs stands between
# `import`, the path, `as` and the name, however the line is indented and
# whatever blanks trail it, so long as the lines above it leave the header
# open (`root_reads_as_bend`). The scan trims a line and cuts it at the
# white space bend's loader splits on, JavaScript's `\s`, so spaces and tabs
# are the case the law states and not the only one the scan reads. `ez
# doctor` reads the same roots (`P.roots`), so
# laws/DoctorReportsDrift.bend's import lines are these too.
#
# The one decision the pure half of the lock makes is where a package's
# bytes come from, and a wrong answer there is a lock that rebuilds the
# wrong tree without ever saying so.
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ./defs/Slashless.bend as D1

# LAW: the lock depends on nothing in a World but its Inputs: the ledger it
# is made from (ez.toml, or the one an upgrade leaves), the upgrade's
# refusal, the committed sources, and the verdict on every answer. Two
# Worlds that agree on those write the same bytes to ez.lock.toml, or both
# write none, however they differ otherwise.
law lock_reproducible:
  for w1: W.World
  for w2: W.World
  for e: {W.inputs(w1) == W.inputs(w2) : W.Inputs}
  {P.put(w1, "ez.lock.toml") == P.put(w2, "ez.lock.toml") : P.Wrote}

# LAW: a working checkout, whose git trees are read from BEND_LIB, writes the
# lock a fresh clone writes, which has none there and clones and weighs each
# one at its pinned rev, so long as git hands the clone the same bytes.
law clone_reproduces:
  for +w: W.World
  {P.put(W.reclone(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# The import scan. A root of the lock is a line bend's loader reads as an
# import of a hub package. The loader trims each line of a file's header and
# splits an import at its runs of white space, so what stands between
# `import`, the path, `as` and the name may be any run of spaces and tabs, and
# the line may be indented and may trail blanks.

# a character of a run of white space in an import line
type Gap is Data:
  Sp{}
  Tab{}

# the character a gap stands for
def gap.char(one: Gap) -> Char:
  match one:
    case Sp{}:
      ' '
    case Tab{}:
      '\t'

# a run of spaces and tabs as text
def gap(gs: List<&2, Gap>) -> String:
  match gs:
    case []:
      ""
    case g <> t:
      SCon{gap.char(g), gap(t)}

# whether a string holds no white space, as the path and the name of an
# import do
def solid(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(K.blank(h)), solid(t))

# an import of a hub package as a line of a source file: its indentation,
# `import`, a run of spaces and tabs, `0x<hash>/<path>`, a run, `as`, a run,
# the name, and the blanks that trail it
def hub.line(
  lead: List<&2, Gap>,
  one: List<&2, Gap>,
  hash: String,
  path: String,
  two: List<&2, Gap>,
  three: List<&2, Gap>,
  name: String,
  tail: List<&2, Gap>
) -> String:
  gap(lead) ++ ("import" ++ (gap(one) ++ (("0x" ++ (hash ++ SCon{'/', path}))
    ++ (gap(two) ++ ("as" ++ (gap(three) ++ (name ++ gap(tail))))))))

# LAW: a line bend reads as an import of a hub package names a root of the
# lock, whatever run of spaces and tabs stands between `import` and the path,
# the path and `as`, and `as` and the name, however the line is indented and
# whatever blanks trail it, so long as the lines above it leave the header
# open, and whatever lines follow it. `ez doctor` reads the same roots.
law root_reads_as_bend:
  for +at: String
  for +text: String
  for +pre: List<&2, String>
  for +post: List<&2, String>
  for +ms: List<&2, String>
  for +fs: List<&2, String>
  for +lead: List<&2, Gap>
  for +o: Gap
  for +os: List<&2, Gap>
  for +hash: String
  for +path: String
  for +w: Gap
  for +ws: List<&2, Gap>
  for +r: Gap
  for +rs: List<&2, Gap>
  for +n: Char
  for +ns: String
  for +tail: List<&2, Gap>
  for ez: {String.starts_with(at, ".ez/") == False{} : Bool}
  for ls: {String.lines(text) == List.append(&2, String, pre,
    hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail) <> post)
    : List<&2, String>}
  for hd: {K.scan.walk(pre, K.Head{True{}, [], []}) == K.Head{True{}, ms, fs} : K.Head}
  for +hp: {D1.slashless(hash) == True{} : Bool}
  for hs: {solid(hash) == True{} : Bool}
  for pp: {solid(path) == True{} : Bool}
  for +np: {solid(SCon{n, ns}) == True{} : Bool}
  {L.seen.holds(P.roots.one(W.Source{at, text}), "0x" ++ hash) == True{} : Bool}
