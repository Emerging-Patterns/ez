# `ez publish` publishes under a name when the ledger's `[package]` table
# gives both `publish-as` and `version`: it runs `bend <entry> --publish
# <publish-as>@<version>.0` and, on success, prints the hash and the import
# line by that name. `publish-as` must be a hub name as bend's NAMED rule
# reads one, and `version` MAJOR.MINOR.PATCH with no leading zeros and no
# pre-release or build suffix. With only one of the two keys, or with either
# one malformed, it refuses before it asks git anything or sends anything.
# With neither it publishes by hash as before.
#
# This guarantee is proved over the plan `ez publish` runs
# (`src/pub/plan.bend`). `PP.naming` reads the two `[package]` keys the
# ledger model carries: neither is a publish by hash (`neither_is_hash`),
# one without the other is refused naming the key that is missing
# (`name_needs_version`, `version_needs_name`), a `publish-as` that
# `K.name.part` refuses, the NAMED name rule the package walk already reads
# imports by, is refused (`bad_name_refused`), and so is a `version` that
# `PP.semver` refuses: one with a character other than a digit or a dot
# anywhere (`semver_needs_digits`, `prerelease_refused`, `build_refused`),
# or one that is not three numbers each as `K.ver.num` reads one
# (`bad_version_refused`). Both good are `<publish-as>@<version>.0`
# (`named_is_four_part`). Over a World whose ledger text parses to a model
# with those keys, a refusal stops before git is asked
# (`pub_misnamed_stops`) and its plan is the refusal alone
# (`pub_misnamed_writes_nothing`); a name is asked for in the upload
# question (`pub_named_uploads_named`), and no name asks for the upload by
# hash (`pub_unnamed_uploads_by_hash`); the words the upload runs are
# `upload_by_name` and `upload_by_hash`. A named publish that succeeds
# prints the import line by the name (`pub_reports_name`), and one by hash
# by the hash (`pub_reports_hash`). The two keys read back from the ledger
# ez writes under laws/WrittenLedgerReadsBack.bend, since `Rend.renderable`
# checks them and `ReadsBack` covers the whole model, and the ledger `ez
# init` writes names neither (`init_publishes_by_hash`). What the laws take
# from the interpreter is trusted in src/ez/app.bend: that it runs the words
# `PP.upload.line` makes of the question.
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/lock/plan.bend as P
import ../src/git/git.bend as Git
import ../src/init/plan.bend as IP

# ---------------------------------------------------------------------------
# the name a package is published under

# LAW: a version with a character that is neither a digit nor a dot is not
# MAJOR.MINOR.PATCH, wherever the character stands and whatever is around it
law semver_needs_digits:
  for +pre: String
  for +c: Char
  for +post: String
  for e: {False{} == PP.semver.char(c) : Bool}
  {PP.semver(String.append(pre, SCon{c, post})) == False{} : Bool}

# LAW: so a version with a pre-release suffix is refused, `1.0.0-rc.1` among
# them
law prerelease_refused:
  for +pre: String
  for +post: String
  {PP.semver(String.append(pre, "-" ++ post)) == False{} : Bool}

# LAW: and so is one with build metadata, `1.0.0+abc` among them
law build_refused:
  for +pre: String
  for +post: String
  {PP.semver(String.append(pre, "+" ++ post)) == False{} : Bool}

# LAW: a ledger that gives neither `publish-as` nor `version` publishes by
# hash, as it did before the keys existed
law neither_is_hash:
  for +pa: String
  for +pv: String
  for e0: {True{} == String.is_empty(pa) : Bool}
  for e1: {True{} == String.is_empty(pv) : Bool}
  {PP.naming(pa, pv) == PP.ByHash{} : PP.Named}

# LAW: `publish-as` with no `version` is refused, naming the missing key
law name_needs_version:
  for +pa: String
  for +pv: String
  for e0: {False{} == String.is_empty(pa) : Bool}
  for e1: {True{} == String.is_empty(pv) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.nover(pa)} : PP.Named}

# LAW: and `version` with no `publish-as`
law version_needs_name:
  for +pa: String
  for +pv: String
  for e0: {True{} == String.is_empty(pa) : Bool}
  for e1: {False{} == String.is_empty(pv) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.noname(pv)} : PP.Named}

# LAW: a `publish-as` that is not a hub name as bend's NAMED rule reads one
# (`K.name.part`) is refused, whatever the version
law bad_name_refused:
  for +pa: String
  for +pv: String
  for e0: {False{} == String.is_empty(pa) : Bool}
  for e1: {False{} == String.is_empty(pv) : Bool}
  for en: {False{} == K.name.part(pa) : Bool}
  {PP.naming(pa, pv) == PP.Unnamed{PP.why.name(pa)} : PP.Named}

# LAW: and a good name with a version that is not MAJOR.MINOR.PATCH is refused
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
law upload_by_hash:
  for +entry: String
  {PP.upload.line(entry, "") == ["bend", entry, "--publish"] : List<&2, String>}

# LAW: and one with a name runs `bend <entry> --publish <name>@<version>`,
# which is how bend publishes and names a package in one run
law upload_by_name:
  for +entry: String
  for +nv: String
  for e: {False{} == String.is_empty(nv) : Bool}
  {PP.upload.line(entry, nv) == ["bend", entry, "--publish", nv] : List<&2, String>}

# LAW: `ez publish` on a World whose ledger names the package in a way ez
# refuses refuses outright: it asks git nothing, reads no file and sends
# nothing
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

# LAW: a World whose ledger names the package asks for the upload under that
# name
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
    Git.import.line(nv, PP.at(PW.World{here, Some{text}, rs}))] : List<&2, String>}

# LAW: the ledger `ez init` makes names no `publish-as` and no `version`,
# whatever the package and entry: with `init_ledger_reads_back` it reads back
# with both empty, so the project publishes by hash (`neither_is_hash`) until
# its author names both
law init_publishes_by_hash:
  for +n: String
  for +e: String
  {IP.model(n, e) == M.Manifest{n, e, "", "", "", "", [], []} : M.Manifest}
