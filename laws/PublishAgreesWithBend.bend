# `ez publish` succeeds only when bend exits 0, a line of its output is
# exactly a `0x` name, and every such line equals ez's own hash; it then
# prints that hash and the import line for the entry's path inside the
# package, by the package's name when laws/PublishUnderName.bend gives it
# one and by that hash otherwise. Any other answer exits 1.
import Base
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/lock/plan.bend as P
import ../src/git/git.bend as Git
import ../src/add/world.bend as A

# whether any line of a list is a `0x` name. This is the vocabulary the
# answer laws need and nothing else uses: it says here what "bend printed a
# name" means, in a form Bend can walk, independently of the check that goes
# looking for one.
def any_name.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# the walk itself: a list holds a name when its head is one, or when the rest
# of it does
def any_name(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      False{}
    case +h <> t:
      any_name.step(PP.is_name(h), _u => any_name(t))

# ---------------------------------------------------------------------------
# bend's answer

# LAW: an output with no line that is a `0x` name never agrees. This is the
# law the bash version broke: it grepped for a hash and then, when that
# missed, grepped again for something looser, so an output holding no name
# still produced one.
law unread_never_agrees:
  for +ours: String
  for ls: List<&2, String>
  for e: {False{} == any_name(ls) : Bool}
  {PP.agrees(ours, ls) == False{} : Bool}

# LAW: an output with a line that is a `0x` name other than ez's never
# agrees, wherever that line is and whatever the other lines say, one that
# is ez's hash included. This is the one that matters most, because the
# happy path passes without it.
law differs_never_agrees:
  for +ours: String
  for +pre: List<&2, String>
  for +h: String
  for +post: List<&2, String>
  for e0: {True{} == PP.is_name(h) : Bool}
  for e1: {False{} == String.eq(ours, h) : Bool}
  {PP.agrees(ours, List.append(&2, String, pre, h <> post)) == False{} : Bool}

# LAW: and an output whose one name is ez's hash agrees, whatever else it
# says around it: the shape bend prints, a progress line, the name, and the
# import line.
law ours_agrees:
  for +ours: String
  for +pre: List<&2, String>
  for +h: String
  for +post: List<&2, String>
  for e0: {True{} == PP.is_name(h) : Bool}
  for e1: {True{} == String.eq(ours, h) : Bool}
  for e2: {False{} == any_name(pre) : Bool}
  for e3: {False{} == any_name(post) : Bool}
  {PP.agrees(ours, List.append(&2, String, pre, h <> post)) == True{} : Bool}

# LAW: the line bend prints while it mines is not an answer. bend 2.0.21 says
# `publishing 2 files, 193 bytes, as 0x<hash> (mining its proof of work)`, and
# that line holds a `0x` name in the middle of it. A pattern that looks for a
# hash anywhere in a line finds this one; the anchored one does not.
law progress_is_not_an_answer:
  for rest: String
  {PP.is_name("publishing " ++ rest) == False{} : Bool}

# LAW: nor is the import line bend prints after it. That one holds the name
# too, followed by a path, and it is the line a person is most likely to be
# looking at when they write the pattern.
law import_is_not_an_answer:
  for rest: String
  {PP.is_name("import " ++ rest) == False{} : Bool}

# LAW: a line that does not open `0x` is not a name. The prefix is
# lowercase; an upper-case `0X` is already not one.
law is_name_needs_0x:
  for +s: String
  for e: {False{} == String.starts_with(s, "0x") : Bool}
  {PP.is_name(s) == False{} : Bool}

# LAW: nor is a line of the right prefix whose length is not
# `name.length`. One character short is enough.
law is_name_needs_length:
  for +s: String
  for e0: {True{} == String.starts_with(s, "0x") : Bool}
  for e1: {False{} == Nat.is_eq(String.length(s), PP.name.length()) : Bool}
  {PP.is_name(s) == False{} : Bool}

# LAW: nor is a name of the right prefix and length whose alphabet is
# not lowercase hex. A character no digest holds is enough.
law is_name_needs_hex:
  for +s: String
  for e0: {True{} == String.starts_with(s, "0x") : Bool}
  for e1: {True{} == Nat.is_eq(String.length(s), PP.name.length()) : Bool}
  for e2: {False{} == Git.hex.all(String.to_list(String.drop(s, 2n))) : Bool}
  {PP.is_name(s) == False{} : Bool}

# LAW: a `0x` prefix, the exact length, and a lowercase hex digest are
# a name, and nothing else of the line is read.
law is_name_hex34:
  for +s: String
  for e0: {True{} == String.starts_with(s, "0x") : Bool}
  for e1: {True{} == Nat.is_eq(String.length(s), PP.name.length()) : Bool}
  for e2: {True{} == Git.hex.all(String.to_list(String.drop(s, 2n))) : Bool}
  {PP.is_name(s) == True{} : Bool}

# LAW: `ez publish` succeeds only on a World whose upload bend finished with
# exit 0 and whose output agrees with the hash ez computed (`PP.agrees`):
# every other answer is a plan that refuses, and exits 1
law pub_needs_agreement:
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds(w) == False{} : Bool}

# LAW: and a publish that succeeds says the hash ez computed, never the one
# bend printed, and then the import line for the entry's path inside the
# package, by the name it was published under or by that hash (`PP.called`)
law pub_reports_ours:
  for +w: PW.World
  for ok: {PP.succeeds(w) == True{} : Bool}
  {P.said(PP.plan(w)) == [PP.hash(w), Git.import.line(PP.called(w), PP.at(w))]
    : List<&2, String>}

# LAW: and one by hash says the hash and the import line by the hash, as
# `ez publish` said before a package could have a name
law pub_reports_hash:
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
  for ok: {PP.succeeds(PW.World{here, Some{text}, rs}) == True{} : Bool}
  {P.said(PP.plan(PW.World{here, Some{text}, rs})) == [PP.hash(PW.World{here, Some{text}, rs}),
    Git.import.line(PP.hash(PW.World{here, Some{text}, rs}), PP.at(PW.World{here, Some{text}, rs}))] : List<&2, String>}
