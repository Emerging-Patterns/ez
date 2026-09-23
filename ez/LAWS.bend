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
import ../manifest/manifest.bend as M
import ./pin.bend as Pin
import ./cmd.bend as Cmd
import ../pkg/path.bend as P
import ./named.bend as Named

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

# LAW: an absolute path is fetched as it is, wherever ez was run
law anchor_absolute:
  for here: String
  for +rest: String
  {Tgt.anchor(here, "/" ++ rest) == "/" ++ rest : String}

# LAW: a relative path is taken from the directory ez was run in, and not
# from the work directory git is handed it in
law anchor_relative:
  for +here: String
  for +path: String
  for e: {False{} == String.starts_with(path, "/") : Bool}
  {Tgt.anchor(here, path) == P.join(here, path) : String}

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

# cmd: the files a lock starts from are the ones git tracks

# LAW: a tracked path under `.ez/` is never a root of the lock. The trees
# there are packages, read as packages, and not the project's own sources.
law root_skips_ez:
  for +p: String
  {Cmd.root.keep(".ez/" ++ p) == [] : List<&2, String>}

# cmd: `ez init` starts a project and never writes over one

# LAW: a ledger already on disk, whatever it holds, leaves `ez init` nothing to
# write, so its dependencies, tools and `bin` survive a second `ez init`
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
law leaf_is_last:
  for p: String
  for +n: String
  for e: {Named.Seen{False{}, n} == Named.last(n) : Named.Seen}
  {Named.leaf(p ++ ("/" ++ n)) == n : String}

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
