# pub: the laws. The human states them; PROOF.bend must prove them.
#
# They come in two layers. The decision functions of `ez publish`
# (pub/plan.bend) say what counts as bend's answer, whether that answer
# agrees with ez's hash, and whether the working tree and the package are
# clean enough to send. The plan laws say what the command does with them:
# stated over the plan the planner makes of a World and the questions it
# asks, so what they say of the plan is what the command does, the
# interpreter's faithfulness being EZ-TRUST-2.
#
# `PP.stops(w)` is a World the command refuses outright, asking nothing more
# and sending nothing; `PP.sends(w)` a World at the upload or past it;
# `PP.succeeds(w)` one whose plan ends in success.
import Base
import ./world.bend as PW
import ./plan.bend as PP
import ../lock/plan.bend as P
import ../git/git.bend as G
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ./blurb.bend as B

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
# EZ-PUB-2
law unread_never_agrees:
  for +ours: String
  for ls: List<&2, String>
  for e: {False{} == any_name(ls) : Bool}
  {PP.agrees(ours, ls) == False{} : Bool}

# LAW: an output with a line that is a `0x` name other than ez's never
# agrees, wherever that line is and whatever the other lines say, one that
# is ez's hash included. This is the one that matters most, because the
# happy path passes without it.
# EZ-PUB-2
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
# EZ-PUB-2
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
# EZ-PUB-2
law progress_is_not_an_answer:
  for rest: String
  {PP.is_name("publishing " ++ rest) == False{} : Bool}

# LAW: nor is the import line bend prints after it. That one holds the name
# too, followed by a path, and it is the line a person is most likely to be
# looking at when they write the pattern.
# EZ-PUB-2
law import_is_not_an_answer:
  for rest: String
  {PP.is_name("import " ++ rest) == False{} : Bool}

# LAW: a line that does not open `0x` is not a name. The prefix is
# lowercase; an upper-case `0X` is already not one.
# EZ-PUB-2
law is_name_needs_0x:
  for +s: String
  for e: {False{} == String.starts_with(s, "0x") : Bool}
  {PP.is_name(s) == False{} : Bool}

# LAW: nor is a line of the right prefix whose length is not
# `name.length`. One character short is enough.
# EZ-PUB-2
law is_name_needs_length:
  for +s: String
  for e0: {True{} == String.starts_with(s, "0x") : Bool}
  for e1: {False{} == Nat.is_eq(String.length(s), PP.name.length()) : Bool}
  {PP.is_name(s) == False{} : Bool}

# LAW: nor is a name of the right prefix and length whose alphabet is
# not lowercase hex. A character no digest holds is enough.
# EZ-PUB-2
law is_name_needs_hex:
  for +s: String
  for e0: {True{} == String.starts_with(s, "0x") : Bool}
  for e1: {True{} == Nat.is_eq(String.length(s), PP.name.length()) : Bool}
  for e2: {False{} == G.hex.all(String.to_list(String.drop(s, 2n))) : Bool}
  {PP.is_name(s) == False{} : Bool}

# LAW: a `0x` prefix, the exact length, and a lowercase hex digest are
# a name, and nothing else of the line is read.
# EZ-PUB-2
law is_name_hex34:
  for +s: String
  for e0: {True{} == String.starts_with(s, "0x") : Bool}
  for e1: {True{} == Nat.is_eq(String.length(s), PP.name.length()) : Bool}
  for e2: {True{} == G.hex.all(String.to_list(String.drop(s, 2n))) : Bool}
  {PP.is_name(s) == True{} : Bool}

# ---------------------------------------------------------------------------
# the working tree and the package

# LAW: a tree is clean exactly when `git status --porcelain` named no path at
# all. The two walks are written independently, one looking for a line that
# says something and the other checking that every line says nothing, and this
# holds them to each other. What it pins down is the edge the whole refusal
# turns on: the empty line `String.lines` makes of a trailing newline is not a
# change, and every other line is, whatever its status code says.
# EZ-PUB-1
law clean_is_all_blank:
  for ls: List<&2, String>
  {PP.blanks(ls) == Bool.not(PP.dirty.lines(ls)) : Bool}

# LAW: a status that names an untracked file is a dirty tree
# EZ-PUB-1
law untracked_is_dirty:
  for path: String
  for rest: List<&2, String>
  {PP.dirty.lines(("?? " ++ path) <> rest) == True{} : Bool}

# LAW: and a modified file, ` M`
# EZ-PUB-1
law modified_is_dirty:
  for path: String
  for rest: List<&2, String>
  {PP.dirty.lines((" M " ++ path) <> rest) == True{} : Bool}

# LAW: and a staged addition, `A `
# EZ-PUB-1
law staged_is_dirty:
  for path: String
  for rest: List<&2, String>
  {PP.dirty.lines(("A  " ++ path) <> rest) == True{} : Bool}

# LAW: a file `git ls-files -v` marks `h`, assumed unchanged, is not tracked
# for publishing: `git status` does not report its changes, so its text on
# disk need not be the commit's
# EZ-PUB-1
law assumed_is_untracked:
  for +path: String
  for rest: List<&2, String>
  {PP.tracked.has(("h " ++ path) <> rest, path) == PP.tracked.has(rest, path) : Bool}

# LAW: nor is one it marks `S`, skipped in the worktree, for the same reason
# EZ-PUB-1
law skipped_is_untracked:
  for +path: String
  for rest: List<&2, String>
  {PP.tracked.has(("S " ++ path) <> rest, path) == PP.tracked.has(rest, path) : Bool}

# ---------------------------------------------------------------------------
# the plan

# LAW: `ez publish` on a World whose `git status --porcelain
# --untracked-files=normal` names a path refuses outright: it reads no file
# of the package, asks git nothing more, and sends nothing
# EZ-PUB-1
law pub_dirty_refuses:
  for +w: PW.World
  for +text: String
  for e0: {PP.status(w) == PP.Said{text} : PP.Status}
  for e1: {PP.dirty(text) == True{} : Bool}
  {PP.stops(w) == True{} : Bool}

# LAW: and so does a World in which git could not answer that status: a
# directory in no repository has no commit for the package to exist in
# EZ-PUB-1
law pub_gitless_refuses:
  for +w: PW.World
  for +why: String
  for e: {PP.status(w) == PP.StatusNo{why} : PP.Status}
  {PP.stops(w) == True{} : Bool}

# LAW: a package holding a file git does not track, an ignored one the entry
# imports among them, never gets as far as the upload
# EZ-PUB-1
law pub_stray_sends_nothing:
  for +w: PW.World
  for +path: String
  for e: {PP.stray(w) == PP.Stray{path} : PP.Kept}
  {PP.sends(w) == False{} : Bool}

# LAW: a World the command refuses outright sends nothing
# EZ-PUB-1
law pub_stop_sends_nothing:
  for +w: PW.World
  for r: {PP.stops(w) == True{} : Bool}
  {PP.sends(w) == False{} : Bool}

# LAW: and a World that never gets as far as the upload refuses: its plan
# does not succeed, so the command exits 1
# EZ-PUB-1
law pub_unsent_refuses:
  for +w: PW.World
  for r: {PP.sends(w) == False{} : Bool}
  {PP.succeeds(w) == False{} : Bool}

# LAW: `ez publish` succeeds only on a World whose upload bend finished with
# exit 0 and whose output agrees with the hash ez computed (`PP.agrees`):
# every other answer is a plan that refuses, and exits 1
# EZ-PUB-2
law pub_needs_agreement:
  for +w: PW.World
  for e: {PP.agreed(w) == False{} : Bool}
  {PP.succeeds(w) == False{} : Bool}

# LAW: and a publish that succeeds says the hash ez computed, never the one
# bend printed, and then the import line for the entry's path inside the
# package, by the name it was published under or by that hash (`PP.called`)
# EZ-PUB-2
law pub_reports_ours:
  for +w: PW.World
  for ok: {PP.succeeds(w) == True{} : Bool}
  {P.said(PP.plan(w)) == [PP.hash(w), G.import.line(PP.called(w), PP.at(w))]
    : List<&2, String>}

# LAW: `ez publish` that refuses writes nothing: its plan has no effect but
# the lines it says, and a refused one says none
# EZ-OUT-2
law pub_refusal_writes_nothing:
  for +w: PW.World
  for r: {PP.refuses(w) == True{} : Bool}
  {P.writes(PP.plan(w)) == False{} : Bool}

# LAW: `ez publish` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
# EZ-OUT-1
law pub_exits_as_it_refuses:
  for +w: PW.World
  {P.code(PP.plan(w)) == P.status.of(PP.refuses(w)) : U32}

# LAW: with no ez.toml, `ez publish` refuses outright, sending nothing,
# rather than guessing an entry
law pub_needs_ledger:
  for +here: String
  for rs: List<&2, PW.Reply>
  {PP.stops(PW.World{here, None{}, rs}) == True{} : Bool}

# ---------------------------------------------------------------------------
# the name a package is published under

# LAW: a version with a character that is neither a digit nor a dot is not
# MAJOR.MINOR.PATCH, wherever the character stands and whatever is around it
# EZ-PUB-3
law semver_needs_digits:
  for +pre: String
  for +c: Char
  for +post: String
  for e: {False{} == PP.semver.char(c) : Bool}
  {PP.semver(String.append(pre, SCon{c, post})) == False{} : Bool}

# LAW: so a version with a pre-release suffix is refused, `1.0.0-rc.1` among
# them
# EZ-PUB-3
law prerelease_refused:
  for +pre: String
  for +post: String
  {PP.semver(String.append(pre, "-" ++ post)) == False{} : Bool}

# LAW: and so is one with build metadata, `1.0.0+abc` among them
# EZ-PUB-3
law build_refused:
  for +pre: String
  for +post: String
  {PP.semver(String.append(pre, "+" ++ post)) == False{} : Bool}

# LAW: a ledger that gives neither `publish-as` nor `version` publishes by
# hash, as it did before the keys existed
# EZ-PUB-3
law neither_is_hash:
  for +pa: String
  for +pv: String
  for e0: {True{} == String.is_empty(pa) : Bool}
  for e1: {True{} == String.is_empty(pv) : Bool}
  {PP.naming(pa, pv) == PP.ByHash{} : PP.Named}

# LAW: `publish-as` with no `version` is refused, naming the missing key
# EZ-PUB-3
law name_needs_version:
  for +pa: String
  for +pv: String
  for e0: {False{} == String.is_empty(pa) : Bool}
  for e1: {True{} == String.is_empty(pv) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.nover(pa)} : PP.Named}

# LAW: and `version` with no `publish-as`
# EZ-PUB-3
law version_needs_name:
  for +pa: String
  for +pv: String
  for e0: {True{} == String.is_empty(pa) : Bool}
  for e1: {False{} == String.is_empty(pv) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.noname(pv)} : PP.Named}

# LAW: a `publish-as` that is not a hub name as bend's NAMED rule reads one
# (`K.name.part`) is refused, whatever the version
# EZ-PUB-3
law bad_name_refused:
  for +pa: String
  for +pv: String
  for e0: {False{} == String.is_empty(pa) : Bool}
  for e1: {False{} == String.is_empty(pv) : Bool}
  for en: {False{} == K.name.part(pa) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.name(pa)} : PP.Named}

# LAW: and a good name with a version that is not MAJOR.MINOR.PATCH is refused
# EZ-PUB-3
law bad_version_refused:
  for +pa: String
  for +pv: String
  for e0: {False{} == String.is_empty(pa) : Bool}
  for e1: {False{} == String.is_empty(pv) : Bool}
  for en: {True{} == K.name.part(pa) : Bool}
  for ev: {False{} == PP.semver(pv) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}

# LAW: a good name and a good version name the package
# `<publish-as>@<version>.0`, the version with bend's fourth number after it
# EZ-PUB-3
law named_is_four_part:
  for +pa: String
  for +pv: String
  for e0: {False{} == String.is_empty(pa) : Bool}
  for e1: {False{} == String.is_empty(pv) : Bool}
  for en: {True{} == K.name.part(pa) : Bool}
  for ev: {True{} == PP.semver(pv) : Bool}
  {PP.naming(pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"} : PP.Named}

# LAW: the upload of a package with no name runs `bend <entry> --publish`,
# the words ez ran before a package could have one
# EZ-PUB-3
law upload_by_hash:
  for +entry: String
  {PP.upload.line(entry, "") == ["bend", entry, "--publish"] : List<&2, String>}

# LAW: and one with a name runs `bend <entry> --publish <name>@<version>`,
# which is how bend publishes and names a package in one run
# EZ-PUB-3
law upload_by_name:
  for +entry: String
  for +nv: String
  for e: {False{} == String.is_empty(nv) : Bool}
  {PP.upload.line(entry, nv) == ["bend", entry, "--publish", nv] : List<&2, String>}

# LAW: `ez publish` on a World whose ledger names the package in a way ez
# refuses refuses outright: it asks git nothing, reads no file and sends
# nothing
# EZ-PUB-3
law pub_misnamed_stops:
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
  for +why: String
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.Unnamed{why} : PP.Named}
  {PP.stops(PW.World{here, Some{text}, rs}) == True{} : Bool}

# LAW: and its plan is that refusal and nothing else, so it writes nothing
# EZ-OUT-2
law pub_misnamed_writes_nothing:
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
  for +why: String
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.Unnamed{why} : PP.Named}
  {PP.plan(PW.World{here, Some{text}, rs}) == P.Plan{[], P.Refused{why}} : P.Plan}

# LAW: a World whose ledger names the package asks for the upload under that
# name
# EZ-PUB-3
law pub_named_uploads_named:
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
  {PP.upload(PW.World{here, Some{text}, rs}) == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), nv,
    PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}

# LAW: and one whose ledger names none asks for the upload by hash
# EZ-PUB-3
law pub_unnamed_uploads_by_hash:
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
  {PP.upload(PW.World{here, Some{text}, rs}) == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), "",
    PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}

# LAW: a named publish that succeeds says the hash ez computed, then the
# import line by the name it was published under
# EZ-PUB-3
law pub_reports_name:
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
  for ok: {PP.succeeds(PW.World{here, Some{text}, rs}) == True{} : Bool}
  {P.said(PP.plan(PW.World{here, Some{text}, rs})) == [PP.hash(PW.World{here, Some{text}, rs}),
    G.import.line(nv, PP.at(PW.World{here, Some{text}, rs}))] : List<&2, String>}

# LAW: and one by hash says the hash and the import line by the hash, as
# `ez publish` said before a package could have a name
# EZ-PUB-2
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
  for +ts: List<&2, M.Tool>
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.ByHash{} : PP.Named}
  for ok: {PP.succeeds(PW.World{here, Some{text}, rs}) == True{} : Bool}
  {P.said(PP.plan(PW.World{here, Some{text}, rs})) == [PP.hash(PW.World{here, Some{text}, rs}),
    G.import.line(PP.hash(PW.World{here, Some{text}, rs}), PP.at(PW.World{here, Some{text}, rs}))] : List<&2, String>}

# ---------------------------------------------------------------------------
# the hub description

# LAW: a text's first line is what comes before its first newline: a line
# with no newline in it, then a newline, then anything, has that line first
# EZ-PUB-4
law line_first_cut:
  for a: String
  for +b: String
  for one: {B.has.nl(a) == False{} : Bool}
  {B.line.first(a ++ "\n" ++ b) == a : String}

# LAW: a file named LICENSE at the top of the package is one the hub passes
# over
# EZ-PUB-4
law hub_license_named:
  for +t: String
  {B.lic(K.Source{"LICENSE", t}) == True{} : Bool}

# LAW: a LICENSE, wherever it stands in the package, never gives the
# description: the package describes itself as it would without it
# EZ-PUB-4
law hub_skips_license:
  for +p: String
  for +t: String
  for fs: List<&2, K.Source>
  for l: {B.lic(K.Source{p, t}) == True{} : Bool}
  {B.blurb(K.Source{p, t} <> fs) == B.blurb(fs) : String}

# LAW: a file that is not a LICENSE, whose path comes no later than any other
# file's, gives the description: its own first line, wherever the walk found
# it
# EZ-PUB-4
law hub_first_by_path:
  for +p: String
  for +t: String
  for fs: List<&2, K.Source>
  for nl: {B.lic(K.Source{p, t}) == False{} : Bool}
  for af: {B.after(p, fs) == True{} : Bool}
  {B.blurb(K.Source{p, t} <> fs) == B.line.first(t) : String}

# LAW: the upload is asked for with that line, the description of the
# package the walk made, and it is the only question that carries one, so a
# publish refused before the upload (`pub_stop_sends_nothing`,
# `pub_stray_sends_nothing`) says nothing but why
# EZ-PUB-4
law pub_upload_says_description:
  for +w: PW.World
  {PP.upload(w) == PW.Upload{PP.entry(w), PP.named.word(PP.named(w)),
    "hub description: " ++ B.blurb(PP.files.of(PP.walked(w)))} : PW.Ask}
