# ez: the laws. The human states them; PROOF.bend must prove them. The string
# facts a test run turns on live here: what bend's own chatter is, what a `#|`
# trailer asks for, and which `0x` name an import line wrote. The clock's
# by.effect deadline lives here too, and the command line as parse sees it.
# The OS half of the clock is not among them.
import Base
import ./quiet.bend as Q
import ./drift.bend as D
import ./gate.bend as G
import ./clock.bend as Clock
import ./args.bend as Args
import ./target.bend as Tgt
import ./key.bend as K
import ../manifest/manifest.bend as M
import ../ez/pin.bend as Pin
import ./cmd.bend as Cmd
import ./env.bend as Env
import ./doctor.bend as Doctor
import ../pkg/path.bend as P
import ./named.bend as Named
import ../manifest/render.bend as Rend

# a ledger naming two packages, the one the drift laws read
def ledger() -> String:
  "[package]\nname = \"app\"\nentry = \"main.bend\"\n" ++
  "\n[deps.sha256]\nhash = \"0xaaaa\"\n" ++
  "\n[deps.wire]\nhash = \"0xbbbb\"\n"

# quiet: bend's chatter is not the program's output

# LAW: a line that does not open as bend's update nag is not one. The match
# is anchored at the front, so a test that prints the words `bend update` in
# prose is still compared on them.
law nag_needs_prefix:
  for +s: String
  for e: {False{} == String.starts_with(s, "bend ") : Bool}
  {Q.is_nag(s) == False{} : Bool}

# LAW: the check report's first line is a report line even when nothing
# before it was. Both wordings open with these words.
law report_opens:
  for +rest: String
  {Q.in_report(False{}, "All terms check" ++ rest) == True{} : Bool}

# LAW: a dash line is a report line only when the line before it was. This is
# the 2.0.18 list; a program's own `- ` line is not in that list.
law dash_follows_report:
  for +rest: String
  {Q.in_report(True{}, "- " ++ rest) == True{} : Bool}

# LAW: and a dash line that is not after the report is the program's.
law dash_alone_is_output:
  for rest: String
  {Q.in_report(False{}, "- " ++ rest) == False{} : Bool}

# trailer: what a test file states its run must print

# LAW: a line that does not open with `#|` is not a trailer line
law want_skips:
  for +h: String
  for +t: List<&2, String>
  for e: {False{} == String.starts_with(h, "#|") : Bool}
  {G.want(h <> t) == G.want(t) : List<&2, String>}

# LAW: a trailer line is kept with the `#|` dropped
law want_keeps:
  for +rest: String
  for +t: List<&2, String>
  {G.want(("#|" ++ rest) <> t) == rest <> G.want(t) : List<&2, String>}

# drift: the ledger against the import lines

# LAW: a line that is not a hub import names no package
law hash_of_local:
  for +s: String
  for e: {False{} == String.starts_with(s, "import 0x") : Bool}
  {D.hash_of(s) == "" : String}

# LAW: an import line names its package
# toward EZ-VEN-5
law hash_of_import:
  {D.hash_of("import 0xaaaa/sha256.bend as S") == "0xaaaa" : String}

# LAW: a local import names none
# toward EZ-VEN-5
law hash_of_relative:
  {D.hash_of("import ./run.bend as R") == "" : String}

# LAW: the same package imported twice counts once
# toward EZ-VEN-5
law imported_dedups:
  {D.imported(["import 0xaaaa/a.bend as A", "import 0xaaaa/b.bend as B"])
    == ["0xaaaa"] : List<&2, String>}

# LAW: a ledger the source agrees with has no drift
# toward EZ-VEN-5
law report_agrees:
  {D.report(["import 0xaaaa/s.bend as S", "import 0xbbbb/w.bend as W"],
    M.parse(ledger())) == [] : List<&2, String>}

# LAW: a hash the ledger does not name is drift, and so is a ledger entry
# nobody imports
# toward EZ-VEN-5
law report_both_ways:
  {D.report(["import 0xaaaa/s.bend as S", "import 0xcccc/x.bend as X"],
    M.parse(ledger()))
    == ["drift: 0xcccc is imported but ez.toml does not name it",
      "drift: wire = 0xbbbb is in ez.toml but no import line uses it"]
    : List<&2, String>}

# LAW: a ledger entry nobody imports is drift
# toward EZ-VEN-5
law report_unused:
  {D.report(["import 0xaaaa/s.bend as S"], M.parse(ledger()))
    == ["drift: wire = 0xbbbb is in ez.toml but no import line uses it"]
    : List<&2, String>}

# clock: the deadline the run effect holds. `date` and `test` are not
# among them.

# LAW: the deadline the run effect keeps is the absolute second
law by_effect_keeps:
  for +d: String
  for e: {False{} == String.is_empty(d) : Bool}
  {Clock.by.effect(d) == d : String}

# the command line as parse sees it, and the words `run` forwards

# LAW: a `run` line is parsed as the command alone
# toward EZ-TOOL-9
law argv_of_run:
  {Args.argv.of(["run", "x", "--flag"]) == ["run"] : List<&2, String>}

# LAW: `tool run` is parsed as the command and its target. The words after
# the target are not flags of ez.
# toward EZ-TOOL-9
law argv_of_tool:
  {Args.argv.of(["tool", "run", "Emerging-Patterns/bolt", "--", "a"])
    == ["tool", "run", "Emerging-Patterns/bolt"] : List<&2, String>}

# LAW: a leading `--` is not a word the program was given
# toward EZ-TOOL-9
law tool_rest_dashes:
  {Args.tool.rest(["tool", "run", "Emerging-Patterns/bolt", "--", "a", "--b"])
    == ["a", "--b"] : List<&2, String>}

# LAW: words after the target are forwarded when no separator was written
# toward EZ-TOOL-9
law tool_rest_plain:
  {Args.tool.rest(["tool", "run", "o/r", "a"]) == ["a"] : List<&2, String>}

# target: what a word names. The four ways a word can name something are
# each a law over every word of that shape, and together they are EZ-RES-3.

# LAW: a target with `://` in it is a git URL, whatever is around it
# EZ-RES-3
law classify_url:
  for +a: String
  for +b: String
  {Tgt.classify(a ++ ("://" ++ b))
    == Tgt.remote(a ++ ("://" ++ b), Tgt.slug.url(a ++ ("://" ++ b)))
    : Tgt.Place}

# LAW: a target starting `git@` is a git URL
# EZ-RES-3
law classify_scp:
  for +rest: String
  for e: {False{} == String.contains("git@" ++ rest, "://") : Bool}
  {Tgt.classify("git@" ++ rest)
    == Tgt.remote("git@" ++ rest, Tgt.slug.scp("git@" ++ rest)) : Tgt.Place}

# LAW: a target starting `/` is a path
# EZ-RES-3
law classify_abs:
  for +rest: String
  for e: {False{} == String.contains("/" ++ rest, "://") : Bool}
  {Tgt.classify("/" ++ rest) == Tgt.Local{"/" ++ rest} : Tgt.Place}

# LAW: a target starting `./` is a path, even when what follows is
# `owner/repo`
# EZ-RES-3
law classify_here:
  for +rest: String
  for e: {False{} == String.contains("./" ++ rest, "://") : Bool}
  {Tgt.classify("./" ++ rest) == Tgt.Local{"./" ++ rest} : Tgt.Place}

# LAW: a target starting `../` is a path
# EZ-RES-3
law classify_up:
  for +rest: String
  for e: {False{} == String.contains("../" ++ rest, "://") : Bool}
  {Tgt.classify("../" ++ rest) == Tgt.Local{"../" ++ rest} : Tgt.Place}

# LAW: a target starting `~/` is a path
# EZ-RES-3
law classify_home:
  for +rest: String
  for e: {False{} == String.contains("~/" ++ rest, "://") : Bool}
  {Tgt.classify("~/" ++ rest) == Tgt.Local{"~/" ++ rest} : Tgt.Place}

# LAW: two segments of letters, digits, `-`, `_` and `.`, neither of them `.`
# or `..`, and the second not ending in `.bend`, are that repository on
# GitHub. `vercel/next.js` is one, and so is `o/r.git`, which is cached without
# its `.git` as its URL would be. `src/main.bend` is not.
# EZ-RES-3
law classify_github:
  for +a: String
  for +b: String
  for ea: {Tgt.seg(a) == True{} : Bool}
  for eb: {Tgt.seg(b) == True{} : Bool}
  for ef: {Tgt.bend.file(b) == False{} : Bool}
  {Tgt.classify(a ++ ("/" ++ b))
    == Tgt.Remote{"https://github.com/" ++ (a ++ ("/" ++ b)),
      "github.com/" ++ Tgt.ungit(a ++ ("/" ++ b))} : Tgt.Place}

# LAW: anything else is a path: a word with no `://`, not starting `git@`,
# `/`, `./`, `../` or `~/`, and not two such segments around a slash with
# the second not ending in `.bend`. The
# empty word is not a target at all, and is refused.
# EZ-RES-3
law classify_else:
  for +text: String
  for ne: {False{} == String.is_empty(text) : Bool}
  for eu: {False{} == String.contains(text, "://") : Bool}
  for eg: {False{} == String.starts_with(text, "git@") : Bool}
  for e1: {False{} == String.starts_with(text, "/") : Bool}
  for e2: {False{} == String.starts_with(text, "./") : Bool}
  for e3: {False{} == String.starts_with(text, "../") : Bool}
  for e4: {False{} == String.starts_with(text, "~/") : Bool}
  for no: @a:String -> @b:String -> {text == a ++ ("/" ++ b) : String}
    -> {Tgt.seg(a) == True{} : Bool} -> {Tgt.seg(b) == True{} : Bool}
    -> {Tgt.bend.file(b) == False{} : Bool} -> Empty
  {Tgt.classify(text) == Tgt.Local{text} : Tgt.Place}

# LAW: a slug that would leave the cache is refused
# toward EZ-TOOL-8
law target_escapes:
  {Tgt.show(Tgt.classify("https://example.com/../../tmp"))
    == "bad not a repository" : String}

# LAW: `~/…` expands under the home directory
law expand_home:
  for +home: String
  for +rest: String
  {Tgt.expand(home, "~/" ++ rest) == home ++ ("/" ++ rest) : String}

# LAW: a URL is fetched as it is, wherever ez was run
# EZ-LED-8
law anchor_url:
  for here: String
  for +a: String
  for +b: String
  {P.anchor(here, a ++ ("://" ++ b)) == a ++ ("://" ++ b) : String}

# LAW: an absolute path is fetched as it is, wherever ez was run
# EZ-LED-8
law anchor_absolute:
  for here: String
  for +rest: String
  for e: {False{} == String.contains("/" ++ rest, "://") : Bool}
  {P.anchor(here, "/" ++ rest) == "/" ++ rest : String}

# LAW: a relative path, which the ledger keeps as it was given, is taken from
# the directory ez runs in, the project's, and not from the work directory or
# the repository top git would read it from
# EZ-LED-8
law anchor_relative:
  for +here: String
  for +path: String
  for eu: {False{} == String.contains(path, "://") : Bool}
  for ea: {False{} == String.starts_with(path, "/") : Bool}
  for eg: {False{} == String.starts_with(path, "git@") : Bool}
  {P.anchor(here, path) == P.join(here, path) : String}

# key: when a cached tool is reused. The checkout is its commit; the binary
# is its commit, the file bend built and the bend that built it. Each law
# holds for every key, so no field is ever left out of the comparison.

# LAW: a binary built from another commit is built again
# EZ-TOOL-2
law key_rev_differs:
  for +r0: String
  for +f0: String
  for +b0: String
  for +r1: String
  for +f1: String
  for +b1: String
  for e: {False{} == String.eq(r0, r1) : Bool}
  {K.reuse(K.Key{r0, f0, b0}, K.Key{r1, f1, b1}) == False{} : Bool}

# LAW: a binary built from another file is built again, so a pin's `bin` or
# `entry` and a free run of the same commit do not share one
# EZ-TOOL-2
law key_file_differs:
  for +r0: String
  for +f0: String
  for +b0: String
  for +r1: String
  for +f1: String
  for +b1: String
  for e: {False{} == String.eq(f0, f1) : Bool}
  {K.reuse(K.Key{r0, f0, b0}, K.Key{r1, f1, b1}) == False{} : Bool}

# LAW: a binary another bend built is built again
# EZ-TOOL-2
law key_bend_differs:
  for +r0: String
  for +f0: String
  for +b0: String
  for +r1: String
  for +f1: String
  for +b1: String
  for e: {False{} == String.eq(b0, b1) : Bool}
  {K.reuse(K.Key{r0, f0, b0}, K.Key{r1, f1, b1}) == False{} : Bool}

# LAW: with no commit, whatever was recorded, the binary is built again
# EZ-TOOL-2
law key_no_rev:
  for was: K.Key
  for +f: String
  for +b: String
  {K.reuse(was, K.Key{"", f, b}) == False{} : Bool}

# LAW: a record that did not read, such as one written before the file and
# the bend were recorded, reuses nothing
law key_none_misses:
  for +r: String
  for +f: String
  for +b: String
  for e: {False{} == String.is_empty(r) : Bool}
  {K.reuse(K.none(), K.Key{r, f, b}) == False{} : Bool}

# LAW: the same commit, file and bend reuse the binary
# EZ-TOOL-2
law key_same_reuses:
  for +r: String
  for +f: String
  for +b: String
  for e: {False{} == String.is_empty(r) : Bool}
  {K.reuse(K.Key{r, f, b}, K.Key{r, f, b}) == True{} : Bool}

# LAW: a checkout of another commit is cloned again. The file and the bend
# are not asked.
# EZ-TOOL-2
law checkout_differs:
  for +was: String
  for +now: String
  for e: {False{} == String.eq(was, now) : Bool}
  {K.checkout(was, now) == False{} : Bool}

# LAW: a checkout of this commit is kept
# EZ-TOOL-2
law checkout_same:
  for +r: String
  for e: {False{} == String.is_empty(r) : Bool}
  {K.checkout(r, r) == True{} : Bool}

# LAW: `bin` is the file that is built
# toward EZ-TOOL-7
law file_bin:
  {Tgt.file.of("ez/main.bend", "manifest/manifest.bend") == "ez/main.bend"
    : String}

# LAW: with no `bin`, the entry is built
# toward EZ-TOOL-7
law file_entry:
  {Tgt.file.of("", "bolt/main.bend") == "bolt/main.bend" : String}

# LAW: with neither, the file is `main.bend`
# toward EZ-TOOL-7
law file_default:
  {Tgt.file.of("", "") == "main.bend" : String}

# LAW: a package with no name builds `app`
# toward EZ-TOOL-7
law out_name_empty:
  {Tgt.out.name("") == "app" : String}

# LAW: otherwise the binary is the package's name
# toward EZ-TOOL-7
law out_name:
  {Tgt.out.name("bolt") == "bolt" : String}

# doctor: the lock is judged against the ledger it resolves

# LAW: a ledger with no dependencies never makes the lock a problem, whatever
# the lock names, so `ez doctor` passes a project that has nothing to lock
law lock_needless:
  for hs: List<&2, String>
  {Doctor.lock.wrong(0n, hs) == False{} : Bool}

# LAW: a ledger with dependencies and a lock that names no package is one
law lock_needed:
  for n: Nat
  {Doctor.lock.wrong(1n+n, []) == True{} : Bool}

# LAW: a lock that names a package is never one, however many the ledger has
law lock_names:
  for deps: Nat
  for h: String
  for t: List<&2, String>
  {Doctor.lock.wrong(deps, h <> t) == False{} : Bool}

# env: the directories ez makes before a command runs. Only a command that
# writes into one without making it gets it, so `ez help`, `ez doctor` and a
# mistyped command leave the directory they ran in as they found it.

# LAW: a command other than `check` and `build` has nothing made for it
law dirs_other:
  for +cmd: String
  for +out: String
  for ec: {False{} == String.eq(cmd, "check") : Bool}
  for eb: {False{} == String.eq(cmd, "build") : Bool}
  {Env.dirs(cmd, out) == [] : List<&2, String>}

# LAW: `check` has `.ez` made, where its JS goes
law dirs_check:
  for +cmd: String
  for +out: String
  for ec: {True{} == String.eq(cmd, "check") : Bool}
  {Env.dirs(cmd, out) == [".ez"] : List<&2, String>}

# LAW: `build` told nothing has `bin` made, where its binary goes
law dirs_build:
  for +cmd: String
  for +out: String
  for ec: {False{} == String.eq(cmd, "check") : Bool}
  for eb: {True{} == String.eq(cmd, "build") : Bool}
  for eo: {True{} == String.is_empty(out) : Bool}
  {Env.dirs(cmd, out) == ["bin"] : List<&2, String>}

# LAW: and `build` told where to write has nothing made in the project
law dirs_build_out:
  for +cmd: String
  for +out: String
  for ec: {False{} == String.eq(cmd, "check") : Bool}
  for eb: {True{} == String.eq(cmd, "build") : Bool}
  for eo: {False{} == String.is_empty(out) : Bool}
  {Env.dirs(cmd, out) == [] : List<&2, String>}

# cmd: a command that edits the ledger needs one to be there

# LAW: a missing ledger reads, for any command that edits it, as one that did
# not parse, which renders as nothing, so no edit is ever written in its place
# EZ-LED-6
law ledger_missing_unwritten:
  for +cmd: String
  {Rend.render(Cmd.ledger.of(None{}, cmd)) == "" : String}

# LAW: a ledger that is there is read as the file says
law ledger_present_parsed:
  for s: String
  for cmd: String
  {Cmd.ledger.of(Some{s}, cmd) == M.parse(s) : M.Read}

# cmd: `ez init` starts a project and never writes over one

# LAW: a ledger already on disk, whatever it holds, leaves `ez init` nothing to
# write, so its dependencies, tools and `bin` survive a second `ez init`
# EZ-LED-6
law init_keeps_ledger:
  for s: String
  for name: String
  for at: String
  {Cmd.init.plan(Some{s}, name, at) == None{} : Maybe<&2, String>}

# named: what `ez add` records a dependency under. Its source names it, never
# its entry file; the ledger keeps the name it already gave that source, and
# refuses to hand a name it gave one source to another.

# LAW: a source is named by what follows its last slash, whatever comes
# before. A slug, a url and a resolved directory are all named this way, so
# two packages whose entry is `main.bend` are named after their repositories.
# EZ-LED-7
law leaf_is_last:
  for p: String
  for +n: String
  for e: {Named.Seen{False{}, n} == Named.last(n) : Named.Seen}
  {Named.leaf(p ++ ("/" ++ n)) == n : String}

# LAW: a package whose own `[package] name` is a TOML bare key is named by it
# EZ-LED-7
law own_package:
  for +pkg: String
  for +fresh: String
  for e: {True{} == Named.bare(pkg) : Bool}
  {Named.own(pkg, fresh) == pkg : String}

# LAW: a package name that is not a bare key, or none at all, falls through to
# the name the source gives itself rather than being refused
# EZ-LED-7
law own_invalid:
  for +pkg: String
  for +fresh: String
  for e: {False{} == Named.bare(pkg) : Bool}
  {Named.own(pkg, fresh) == fresh : String}

# LAW: a name with a dot in it, like `next.js`, is not a bare key, since
# `[deps.next.js]` would be a table inside a table
law bare_no_dot:
  for +a: String
  for +b: String
  {Named.bare(a ++ ("." ++ b)) == False{} : Bool}

# LAW: the name the ledger already gives this source beats the package's own
# name and the source's
# EZ-LED-7
law name_keeps:
  for n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for +pkg: String
  for +fresh: String
  {Named.name(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    pkg, fresh) == n : String}

# LAW: `--rename`, when given, is the name, ahead of the ledger's, the
# package's and the source's
# EZ-LED-7
law rename_wins:
  for ds: List<&2, M.Dep>
  for +url: String
  for +rename: String
  for +pkg: String
  for +fresh: String
  for e: {False{} == String.is_empty(rename) : Bool}
  {Named.as(ds, url, rename, pkg, fresh) == rename : String}

# LAW: a `--rename` that is not a bare key, like `a.b`, is refused
# EZ-LED-7
law rename_dotted:
  for +a: String
  for +b: String
  {Named.renamed.ok(a ++ ("." ++ b)) == False{} : Bool}

# LAW: a `--rename` of a source the ledger already records under another name
# is refused, rather than recorded twice or renamed behind the ledger's back
# EZ-LED-7
law rename_moved:
  for +n: String
  for +h: String
  for +en: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +t: List<&2, M.Dep>
  for +rename: String
  for er: {False{} == String.is_empty(rename) : Bool}
  for en0: {False{} == String.is_empty(n) : Bool}
  for nr: {False{} == String.eq(n, rename) : Bool}
  {Named.moved(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    rename) == True{} : Bool}

# LAW: and a `--rename` the ledger gives to another source still clashes
# EZ-LED-7
law rename_clash:
  for +r: String
  for +h: String
  for +en: String
  for +u: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +t: List<&2, M.Dep>
  for +pkg: String
  for +fresh: String
  for ne: {False{} == String.eq(u, url) : Bool}
  for er: {False{} == String.is_empty(r) : Bool}
  {Named.clash(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t,
    Named.as(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, url, r,
      pkg, fresh), url) == True{} : Bool}

# LAW: a ledger that holds no dependency takes the name the source gives
# itself
law had_fresh:
  for url: String
  for fresh: String
  {Named.had([], url, fresh) == fresh : String}

# LAW: a ledger that already holds this git source keeps the name it gave it,
# so adding it again replaces that entry rather than adding a second
law had_keeps:
  for n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for fresh: String
  {Named.had(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    fresh) == n : String}

# LAW: an entry from another git source does not lend this one its name
law had_skips_git:
  for n: String
  for h: String
  for en: String
  for u: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for fresh: String
  for ne: {False{} == String.eq(u, url) : Bool}
  {Named.had(M.Dep{n, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, url,
    fresh) == Named.had(t, url, fresh) : String}

# LAW: nor does a hub entry, which has no git source to be
law had_skips_hub:
  for n: String
  for h: String
  for en: String
  for +url: String
  for t: List<&2, M.Dep>
  for fresh: String
  {Named.had(M.Dep{n, h, en, M.Hub{}} <> t, url, fresh)
    == Named.had(t, url, fresh) : String}

# LAW: an empty ledger clashes with no name
law clash_none:
  for name: String
  for url: String
  {Named.clash([], name, url) == False{} : Bool}

# LAW: an entry of another name is not a clash, whatever its source
law clash_skips:
  for m: String
  for h: String
  for en: String
  for s: M.Source
  for t: List<&2, M.Dep>
  for +name: String
  for +url: String
  for ne: {False{} == String.eq(m, name) : Bool}
  {Named.clash(M.Dep{m, h, en, s} <> t, name, url)
    == Named.clash(t, name, url) : Bool}

# LAW: the name held by this same git source is not a clash: that is a re-add
# EZ-LED-7
law clash_same:
  for +n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  {Named.clash(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, n,
    url) == False{} : Bool}

# LAW: the name held by another git source is a clash, and is refused rather
# than written over
# EZ-LED-7
law clash_other:
  for +n: String
  for h: String
  for en: String
  for u: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ne: {False{} == String.eq(u, url) : Bool}
  {Named.clash(M.Dep{n, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, n,
    url) == True{} : Bool}

# LAW: and so is the name held by a hub dependency
# EZ-LED-7
law clash_hub:
  for +n: String
  for h: String
  for en: String
  for +url: String
  for t: List<&2, M.Dep>
  {Named.clash(M.Dep{n, h, en, M.Hub{}} <> t, n, url) == True{} : Bool}

# pin: a plain `ez lock` copies every `[tools.*]` pin as the ledger has it,
# and refuses one it would have to fill. Filling is `--upgrade`'s alone.

# LAW: a git pin with a commit and a NAR hash is copied as it is. Nothing
# about it asks the lock to reach a remote, so nothing stops the lock.
law gap_of_full_pin:
  for n: String
  for e: String
  for b: String
  for url: String
  for +rev: String
  for tag: String
  for root: String
  for +nar: String
  for vend: Bool
  for fr: {False{} == String.is_empty(rev) : Bool}
  for fn: {False{} == String.is_empty(nar) : Bool}
  {Pin.gap(M.Tool{n, e, b, M.Git{url, rev, tag, root, nar, vend}}) == "" : String}

# LAW: a git pin with no commit is refused, whatever else it holds, and the
# refusal names the upgrade that pins it
law gap_of_revless_pin:
  for +n: String
  for e: String
  for b: String
  for url: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  {Pin.gap(M.Tool{n, e, b, M.Git{url, "", tag, root, nar, vend}})
    == "ez: tools." ++ n ++ " has no rev; run `ez lock --upgrade --package " ++
      n ++ "` to pin it" : String}

# LAW: and one with a commit and no NAR hash is refused the same way
law gap_of_narless_pin:
  for +n: String
  for e: String
  for b: String
  for url: String
  for +rev: String
  for tag: String
  for root: String
  for vend: Bool
  for fr: {False{} == String.is_empty(rev) : Bool}
  {Pin.gap(M.Tool{n, e, b, M.Git{url, rev, tag, root, "", vend}})
    == "ez: tools." ++ n ++ " has no narHash; run `ez lock --upgrade --package " ++
      n ++ "` to pin it" : String}
