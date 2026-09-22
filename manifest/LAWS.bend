# manifest: the laws. The human states them; PROOF.bend must prove them. The
# ledger is a file a person edits, so what matters is that a lookup answers
# with what was written for it, and that the two edits `ez add` and
# `ez remove` make are the edits they claim to be.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ./upgrade.bend as U
import ./ignore.bend as I

# LAW: dropping a dependency drops every entry of that name, so dropping twice
# is dropping once. `ez remove` on a ledger it already edited is a no-op.
law without_idem:
  for ds: List<&2, M.Dep>
  for +name: String
  {R.without(R.without(ds, name), name) == R.without(ds, name) : List<&2, M.Dep>}

# LAW: adding a dependency twice is adding it once, which is what makes
# `ez add` safe to run on a ledger that already names the package.
law add_idem:
  for m: M.Manifest
  for +d: M.Dep
  {R.add(R.add(m, d), d) == R.add(m, d) : M.Manifest}

# The rest of the ledger: the reading of a parsed document into a model, and
# the writing of that model back out. A ledger is a file a person edits, so
# every one of these is a claim about what ez will do with what they wrote.

# whether a document was read into a ledger rather than into a reason
def is_good(read: M.Read) -> Bool:
  match read:
    case M.Bad{why}:
      False{}
    case M.Good{m}:
      True{}

# LAW: a section answers a key with the value written for it, the way a table
# does. `manifest.value` is the table lookup and not a second one.
law value_first_in_section:
  for +k: String
  for v: String
  for ps: List<&2, T.Kv>
  {M.value(T.Kv{k, v} <> ps, k) == v : String}

# LAW: a document answers a section name with the pairs of the first section
# of that name. A later table of the same name never shadows an earlier one,
# which matters because a ledger a person edited may well hold two.
law pairs_of_first:
  for +name: String
  for ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  {M.pairs_of(T.Sect{name, ps} <> ss, name) == ps : List<&2, T.Kv>}

# LAW: a dependency section that names no repo is a hub package. This is the
# one place ez decides that a package needs no checkout, so it must turn on
# the `git` key being absent and on nothing else.
law source_of_hub:
  for +pairs: List<&2, T.Kv>
  for e: {True{} == String.is_empty(M.value(pairs, "git")) : Bool}
  {M.source_of(pairs) == M.Hub{} : M.Source}

# LAW: a git section that names no root is the top of the checkout. A
# ledger written before the `root` key existed can only have meant that,
# and a lock already spells it out as ".".
law source_of_absent_root:
  for +pairs: List<&2, T.Kv>
  for e0: {False{} == String.is_empty(M.value(pairs, "git")) : Bool}
  for e1: {True{} == String.is_empty(M.value(pairs, "root")) : Bool}
  {M.source_of(pairs)
    == M.Git{M.value(pairs, "git"), M.value(pairs, "rev"),
      M.value(pairs, "tag"), ".", M.value(pairs, "narHash"),
      M.flag(M.value(pairs, "vendor"))} : M.Source}

# LAW: a `[deps.<name>]` section is a dependency of that name, with the
# prefix off and nothing else taken with it.
law dep_of_drops_prefix:
  for +name: String
  for +pairs: List<&2, T.Kv>
  {M.dep.name(M.dep_of("deps." ++ name, pairs)) == name : String}

# LAW: a section answers with the name it was written with
law name_of_sect:
  for +n: String
  for ps: List<&2, T.Kv>
  {M.name_of(T.Sect{n, ps}) == n : String}

# LAW: every `[deps.<name>]` section becomes a dependency, in the order the
# document wrote them.
law deps_takes_dep_sections:
  for +name: String
  for +ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  {M.deps(T.Sect{"deps." ++ name, ps} <> ss)
    == M.dep_of("deps." ++ name, ps) <> M.deps(ss) : List<&2, M.Dep>}

# LAW: and a section that is not one is passed over rather than read as one
law deps_skips_other_sections:
  for +n: String
  for ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  for e: {False{} == String.starts_with(n, "deps.") : Bool}
  {M.deps(T.Sect{n, ps} <> ss) == M.deps(ss) : List<&2, M.Dep>}

# LAW: a `[tools.<name>]` section is a pinned CLI of that name, with the
# prefix off and nothing else taken with it.
law tool_of_drops_prefix:
  for +name: String
  for +pairs: List<&2, T.Kv>
  {M.tool.name(M.tool_of("tools." ++ name, pairs)) == name : String}

# LAW: every `[tools.<name>]` section becomes a pinned CLI, in the order the
# document wrote them. A dependency section is not one of them.
law tools_takes_tool_sections:
  for +name: String
  for +ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  {M.tools(T.Sect{"tools." ++ name, ps} <> ss)
    == M.tool_of("tools." ++ name, ps) <> M.tools(ss) : List<&2, M.Tool>}

# LAW: and a section that is not one is passed over
law tools_skips_other_sections:
  for +n: String
  for ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  for e: {False{} == String.starts_with(n, "tools.") : Bool}
  {M.tools(T.Sect{n, ps} <> ss) == M.tools(ss) : List<&2, M.Tool>}

# LAW: a tool section with no hash is not a missing dependency. A hash is
# the `0x` name an import carries, and a tool is not imported.
# toward EZ-LED-5
law tool_needs_no_hash:
  {M.missing([T.Sect{"tools.bolt", [T.Kv{"git", "https://github.com/o/bolt"}]}])
    == "" : String}

# LAW: a `[tools.*]` section is not a dependency
# toward EZ-LED-5
law tool_is_not_a_dep:
  {M.deps([T.Sect{"tools.bolt",
    [T.Kv{"git", "https://github.com/Emerging-Patterns/bolt"},
     T.Kv{"rev", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}]}])
    == [] : List<&2, M.Dep>}

# LAW: a dependency section with no hash is reported, by its own name, before
# any section after it. A hash is the `0x` name the import line carries, so a
# section without one names a package ez cannot resolve.
law missing_finds_first:
  for +n: String
  for +ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  for e0: {True{} == String.starts_with(n, "deps.") : Bool}
  for e1: {True{} == String.is_empty(M.value(ps, "hash")) : Bool}
  {M.missing(T.Sect{n, ps} <> ss) == n : String}

# LAW: a syntax error is reported before a missing hash. A section that did
# not parse cannot be judged for what it holds.
law problem_syntax_first:
  for +bad: String
  for +miss: String
  for e: {False{} == String.is_empty(bad) : Bool}
  {M.problem(bad, miss) == bad : String}

# LAW: once a document is known to be sound, building it cannot fail. Every
# refusal ez makes about a ledger is made by `problem`, and this says `build`
# adds none of its own.
law build_is_good:
  for +ss: List<&2, T.Sect>
  {is_good(M.build(ss)) == True{} : Bool}

# LAW: and a document with any problem at all is never read into a ledger. It
# comes back as the problem, so no command can go on with a half-read file.
law read_refuses_a_problem:
  for +bad: String
  for +ss: List<&2, T.Sect>
  for e: {False{} == String.is_empty(M.problem(bad, M.missing(ss))) : Bool}
  {M.read(bad, ss) == M.Bad{M.problem(bad, M.missing(ss))} : M.Read}

# LAW: the ledger is read out of the sections the parse found and the first
# syntax error it found, and out of nothing else -- not out of the text again.
law parse_reads_the_sections:
  for +text: String
  for bad: String
  for name: String
  for pairs: List<&2, T.Kv>
  for sects: List<&2, T.Sect>
  for e: {T.Toml{bad, name, pairs, sects} == T.parse(text) : T.Toml}
  {M.parse(text) == M.read(bad, sects) : M.Read}

# LAW: a ledger that did not read says so before it says anything else
law show_bad_is_marked:
  for why: String
  {String.starts_with(M.show(M.Bad{why}), "error: ") == True{} : Bool}

# LAW: and one that did opens with the package's own name
law show_good_opens_with_name:
  for +n: String
  for e: String
  for b: String
  for hb: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {String.starts_with(M.show(M.Good{M.Manifest{n, e, b, hb, ds, ts}}), n) == True{}
    : Bool}

# LAW: a lookup answers with the first dependency of that name, whole
law find_first:
  for +n: String
  for h: String
  for en: String
  for s: M.Source
  for t: List<&2, M.Dep>
  {M.find(M.Dep{n, h, en, s} <> t, n) == M.Dep{n, h, en, s} : M.Dep}

# LAW: and a ledger that did not read names no dependency at all, rather than
# the first one it happened to have parsed before it gave up.
law dep_of_unread_is_blank:
  for why: String
  for name: String
  {M.dep(M.Bad{why}, name) == M.Dep{"", "", "", M.Hub{}} : M.Dep}

# LAW: the commit a ledger pins a dependency to is the commit its git section
# wrote. This and the law under it are what `ez lock` and `ez doctor` read,
# and they reach through the lookup, the source and the accessor at once.
law rev_of_names_the_commit:
  for mn: String
  for me: String
  for mb: String
  for mh: String
  for +n: String
  for h: String
  for en: String
  for url: String
  for +rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {M.rev_of(M.Good{M.Manifest{mn, me, mb, mh,
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, ts}}, n) == rev
    : String}

# LAW: and the tag it was asked for is the tag its git section wrote
law tag_of_names_the_tag:
  for mn: String
  for me: String
  for mb: String
  for mh: String
  for +n: String
  for h: String
  for en: String
  for url: String
  for rev: String
  for +tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {M.tag_of(M.Good{M.Manifest{mn, me, mb, mh,
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, ts}}, n) == tag
    : String}

# LAW: a key with no value leaves no trace in the file. An absent tag or entry
# is absent, and never written as an empty string the next read would take for
# a value.
law line_absent:
  for key: String
  {R.line(key, "") == "" : String}

# LAW: so a git source with no tag writes the four keys it does have and
# nothing where the tag would be.
law source_omits_absent_tag:
  for url: String
  for rev: String
  for root: String
  for nar: String
  {R.source(M.Git{url, rev, "", root, nar, False{}})
    == R.line("git", url) ++ R.line("rev", rev) ++ R.line("root", root)
      ++ R.line("narHash", nar) ++ R.line("vendor", "") : String}

# LAW: a dependency's section is headed by that dependency's own name
law dep_opens_its_section:
  for +n: String
  for h: String
  for e: String
  for s: M.Source
  {String.starts_with(R.dep(M.Dep{n, h, e, s}), "\n[deps." ++ n) == True{}
    : Bool}

# LAW: a tool's section is headed by that tool's own name
law tool_opens_its_section:
  for +n: String
  for e: String
  for b: String
  for s: M.Source
  {String.starts_with(R.tool(M.Tool{n, e, b, s}), "\n[tools." ++ n) == True{}
    : Bool}

# LAW: rendering a list of dependencies renders each of them, in order, and
# adds nothing between. Splitting the list splits the text at the same place,
# which is what makes the file the ledger and not a summary of it.
law deps_splits:
  for as: List<&2, M.Dep>
  for +bs: List<&2, M.Dep>
  {R.deps(List.append(&2, M.Dep, as, bs)) == R.deps(as) ++ R.deps(bs) : String}

# LAW: a rendered ledger opens with the package table, so what it writes is a
# document `parse` reads back as a ledger and not as a loose pair.
law show_opens_with_package:
  for n: String
  for e: String
  for b: String
  for hb: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {String.starts_with(R.show(M.Manifest{n, e, b, hb, ds, ts}), "[package]\n") == True{}
    : Bool}

# LAW: a ledger that did not read renders as nothing. `ez add` and `ez remove`
# write what they render, so a failed read that rendered a guess would
# overwrite a good file with it.
law render_of_unread_is_blank:
  for why: String
  {R.render(M.Bad{why}) == "" : String}

# LAW: removing a dependency twice is removing it once, which is what makes
# `ez remove` safe to run on a ledger it already edited.
law remove_idem:
  for m: M.Manifest
  for +name: String
  {R.remove(R.remove(m, name), name) == R.remove(m, name) : M.Manifest}

# LAW: a ledger that did not read locks against bend's own hub. Nothing it
# said can be trusted, so nothing it said picks where packages come from.
law hub_of_unread_is_bends:
  for why: String
  {M.hub_of(M.Bad{why}) == "https://hub.bend-lang.com" : String}

# LAW: and so does one whose `[package]` table names no hub
law hub_of_absent_is_bends:
  for n: String
  for e: String
  for b: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {M.hub_of(M.Good{M.Manifest{n, e, b, "", ds, ts}})
    == "https://hub.bend-lang.com" : String}

# LAW: a hub the ledger names is the hub, whatever else the ledger holds.
# This is the only place `ez lock` learns a hub from, so two checkouts of one
# commit fetch from the same place whatever their environments say.
law hub_of_names_the_hub:
  for n: String
  for e: String
  for b: String
  for +hb: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for f: {False{} == String.is_empty(hb) : Bool}
  {M.hub_of(M.Good{M.Manifest{n, e, b, hb, ds, ts}}) == hb : String}

# LAW: a git section's vendor bit is its `vendor` key read as `true`, and
# nothing else. This is the bit the allowlist is derived from.
law source_of_vendor:
  for +pairs: List<&2, T.Kv>
  for e: {False{} == String.is_empty(M.value(pairs, "git")) : Bool}
  {M.source.vendor(M.source_of(pairs)) == M.flag(M.value(pairs, "vendor"))
    : Bool}

# LAW: a dependency added again keeps the `vendor = true` the ledger already
# gave it. `ez add` has no way to say it, so dropping it would drop the tree
# from the allowlist without anyone having asked.
law readd_keeps_vendor:
  for ds: List<&2, M.Dep>
  for +n: String
  for h: String
  for en: String
  for url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for v: Bool
  for e: {M.source.vendor(M.source.dep(M.find(ds, n))) == True{} : Bool}
  {M.source.vendor(M.source.dep(R.readd(ds,
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, v}}))) == True{} : Bool}

# LAW: the gitignore allowlist names exactly the hashes of the dependencies
# the ledger marks `vendor = true`, in the ledger's order, whatever the file
# said before. `ez add`, `ez remove` and `ez lock --upgrade` write the file
# `I.sync` makes from these lines, so after any of them the allowlist is the
# ledger's and no one else's.
# EZ-VEN-1
law allowlist_is_the_ledger:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  {I.hashes(I.lines(ds, ls)) == I.vended(ds) : List<&2, String>}

# LAW: and every line that is not ez's is kept, in order, as it was written.
# ez's lines are the allowlist, the three rules it needs, and a `.ez/` that
# would make it inert; everything else in the file is the project's.
# EZ-VEN-1
law allowlist_keeps_other_lines:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  {I.others(I.lines(ds, ls)) == I.others(ls) : List<&2, String>}

# a ledger in the form `show` writes: the package table, then each
# dependency, with every value quoted and an absent key left out
def ledger() -> String:
  "[package]\n" ++
  "name = \"myapp\"\n" ++
  "entry = \"src/main.bend\"\n" ++
  "bin = \"src/main.bend\"\n" ++
  "hub = \"https://hub.example\"\n" ++
  "\n[deps.json]\n" ++
  "hash = \"0x1111111111111111111111111111aaaa\"\n" ++
  "\n[deps.wire]\n" ++
  "hash = \"0x7e63a5b990a375c304ed462c071214a6\"\n" ++
  "git = \"https://github.com/owner/repo\"\n" ++
  "rev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
  "tag = \"v1.0\"\n" ++
  "root = \".\"\n" ++
  "narHash = \"sha256-zz\"\n" ++
  "entry = \"src/lib.bend\"\n" ++
  "\n[tools.bolt]\n" ++
  "git = \"https://github.com/Emerging-Patterns/bolt\"\n" ++
  "rev = \"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"\n" ++
  "tag = \"v0.4.0\"\n" ++
  "root = \".\"\n" ++
  "narHash = \"sha256-zz\"\n" ++
  "entry = \"bolt/main.bend\"\n"

# LAW: a rendered ledger reads back as the file it was. `ez add` and
# `ez remove` write what they render, so the file on disk after either
# command is the file the next command will write again.
# toward EZ-LED-4
law render_parse_roundtrip:
  {R.render(M.parse(ledger())) == ledger() : String}

# LAW: the bolt pin in that ledger is a tool, and not a dependency of that name
# toward EZ-LED-5
law bolt_is_a_tool:
  {M.tool.name(M.tool.find(M.tools_of(M.parse(ledger())), "bolt")) == "bolt"
    : String}

# LAW: and its commit is the commit the tool section wrote
# toward EZ-LED-4
law bolt_rev:
  {M.source.rev(M.tool.source(M.tool.find(M.tools_of(M.parse(ledger())), "bolt")))
    == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" : String}

# LAW: a lookup for that name among the dependencies finds none
# toward EZ-LED-5
law bolt_is_not_a_dep:
  {M.dep.name(M.dep(M.parse(ledger()), "bolt")) == "" : String}

# a sha256 pin with a rev and no tag, and the tree committed.
# The tip below is `main` of Giulio2002/bend-sha256 as `ls-remote --symref`
# reported it, which is a descendant of this rev. The latest tag on that
# repo, v0.1.0, is 75741733dca8ba3610b116af5d74997a44c7e978, one commit
# behind that tip. The ledger names no tag, so the upgrade follows the tip.
def sha.toml() -> String:
  "[package]\nname = \"ez\"\nentry = \"manifest/manifest.bend\"\n" ++
  "\n[deps.sha256]\n" ++
  "hash = \"0x0a5c2c95283e42e081da247c84debe18\"\n" ++
  "git = \"https://github.com/Giulio2002/bend-sha256\"\n" ++
  "rev = \"c16cd69cedff0e9e19251401dee1cd973458faef\"\n" ++
  "root = \".\"\n" ++
  "narHash = \"sha256-ZQdxgjNCSu3lXjupIRWD/Xp1+T+H8CyYxmUc/0XLj2s=\"\n" ++
  "vendor = true\n" ++
  "entry = \"sha256.bend\"\n"

# the dependency that stanza reads as
def sha.dep() -> M.Dep:
  M.dep(M.parse(sha.toml()), "sha256")

# `main` at the time the upgrade was written
def sha.tip() -> String:
  "5887e7cefa273ff7f90e3edfd6e90b815bbc79ed"

# LAW: sha256 has no tag, so an upgrade asks the default branch rather than
# a ref the ledger never named
# toward EZ-RES-5
law sha256_aims_forward:
  {U.aim(True{}, M.source.dep(sha.dep())) == U.Forward{} : U.Aim}

# LAW: a hub pin is not upgraded, even when it was the one asked for
# toward EZ-RES-4
law hub_holds:
  {U.aim(True{}, M.Hub{}) == U.Hold{} : U.Aim}

# LAW: a tag is re-resolved, and a neighbour `--package` did not name is not
# toward EZ-RES-8
law tag_follows:
  {U.aim(True{}, M.Git{"https://github.com/Emerging-Patterns/shake",
    "3424b39197335f0aa741e8928dbe5c27b3bde0ef", "v0.1.0", "shake",
    "sha256-JXsEnp4NFlBxM7dNPSCU4TDBuF+d76h5bYgwOd6iu+0=", False{}})
    == U.Follow{"v0.1.0"} : U.Aim}

# LAW: and naming one dependency leaves the other where it was
# toward EZ-RES-6
law unselected_holds:
  {U.aim(False{}, M.source.dep(sha.dep())) == U.Hold{} : U.Aim}

# LAW: sha256's pin, being an ancestor of main, advances to that tip and
# does not grow a tag
# toward EZ-RES-5
law sha256_advances:
  {U.judge(False{}, True{}, True{}, sha.tip(), "")
    == U.Advance{sha.tip(), ""} : U.Verdict}

# LAW: the same commit, recomputed to the same hash, is not a rewrite
# toward EZ-DOC-4
law same_rev_keeps:
  {U.judge(True{}, True{}, True{}, "c16cd69cedff0e9e19251401dee1cd973458faef", "")
    == U.Keep{} : U.Verdict}

# LAW: the same commit whose tree no longer hashes to the pin is drift
# toward EZ-RES-8
law same_rev_drifts:
  {U.judge(True{}, False{}, False{}, "c16cd69cedff0e9e19251401dee1cd973458faef", "")
    == U.Drift{} : U.Verdict}

# LAW: a tag that now names a commit the pin does not descend to has moved
# toward EZ-RES-8
law tag_moved_off:
  {U.judge(False{}, False{}, True{}, "75741733dca8ba3610b116af5d74997a44c7e978",
    "v0.1.0") == U.Off{} : U.Verdict}

# LAW: a move keeps the vendor bit and the entry, and writes the new commit
# toward EZ-RES-5
law sha256_retarget:
  {U.retarget(sha.dep(), sha.tip(), "0xnew", ".", "sha256-new")
    == M.Dep{"sha256", "0xnew", "sha256.bend",
      M.Git{"https://github.com/Giulio2002/bend-sha256", sha.tip(), "", ".",
        "sha256-new", True{}}} : M.Dep}

# a source file that names sha256 twice, names another package, and also
# carries the same digits where they are not that import
def imports.before() -> String:
  "import Base\n" ++
  "import 0x0a5c2c95283e42e081da247c84debe18/sha256.bend as S\n" ++
  "import 0x0a5c2c95283e42e081da247c84debe18/sha256.bend as T\n" ++
  "import 0x1111111111111111111111111111aaaa/json.bend as J\n" ++
  "import 0x0a5c2c95283e42e081da247c84debe18ff/no.bend as N\n" ++
  "import ./local.bend as L\n" ++
  "# import 0x0a5c2c95283e42e081da247c84debe18/sha256.bend as S\n"

# the same file once sha256 and json have moved
def imports.after() -> String:
  "import Base\n" ++
  "import 0xnew/sha256.bend as S\n" ++
  "import 0xnew/sha256.bend as T\n" ++
  "import 0xabc/json.bend as J\n" ++
  "import 0x0a5c2c95283e42e081da247c84debe18ff/no.bend as N\n" ++
  "import ./local.bend as L\n" ++
  "# import 0x0a5c2c95283e42e081da247c84debe18/sha256.bend as S\n"

# LAW: import lines that name a hash that moved name the new one. A longer
# hash, a local import and a comment stay.
# toward EZ-VEN-2
law imports_follow_hash:
  {U.reimport.many(
    [U.Swap{"0x0a5c2c95283e42e081da247c84debe18", "0xnew"},
     U.Swap{"0x1111111111111111111111111111aaaa", "0xabc"}],
    imports.before()) == imports.after() : String}
