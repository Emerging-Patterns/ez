# ez: the laws. The human states them; PROOF.bend must prove them. The string
# and path facts a test run turns on live here: what bend's own chatter is,
# what a `#|` trailer asks for, which `0x` name an import line wrote, and
# where a test sits in the shadow. The clock's on/off and by.effect
# equalities live here too, and the command line as parse sees it. The OS
# half of the clock is not among them.
import Base
import ./quiet.bend as Q
import ./drift.bend as D
import ./gate.bend as G
import ./clock.bend as Clock
import ./args.bend as Args
import ./target.bend as Tgt
import ../ez/say.bend as Say
import ../manifest/manifest.bend as M

# a ledger naming two packages, the one the drift laws read
def ledger() -> String:
  "[package]\nname = \"app\"\nentry = \"main.bend\"\n" ++
  "\n[deps.sha256]\nhash = \"0xaaaa\"\n" ++
  "\n[deps.wire]\nhash = \"0xbbbb\"\n"

# a test file, trailer and all
def source() -> String:
  "import Base\n" ++
  "\n" ++
  "def main() -> IO(Unit):\n" ++
  "  IO.print(\"ok one\")\n" ++
  "\n" ++
  "#|ok one\n" ++
  "#|ok two\n"

# what 2.0.16 prints around a program's output
def old() -> String:
  "ok one\nAll terms check, with 3 unsafe annotations.\nok two\n"

# what 2.0.18 prints: the report, then a line per unsafe def
def new() -> String:
  "ok one\nAll terms check, but 2 defs rely on unsafe or foreign code:\n" ++
  "- snaprun.exec\n- Sha.hex\nok two\n"

# what an aggregate of two tests prints
def output() -> String:
  G.mark() ++ "./ez/tests/one.bend\nok one\nok two\n" ++
    G.mark() ++ "./ez/tests/two.bend\nok three"

# two tests of one project, as one program
def agg() -> String:
  G.agg("ez", ["./ez/tests/one.bend", "./ez/tests/two.bend"])

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

# LAW: nothing printed is nothing
law filter_empty:
  {Q.filter("") == "" : String}

# LAW: the 2.0.16 report goes
law filter_old_report:
  {Q.filter(old()) == "ok one\nok two" : String}

# LAW: the 2.0.18 report and its list go
law filter_new_report:
  {Q.filter(new()) == "ok one\nok two" : String}

# LAW: a program's own dash line survives
law filter_keeps_own_dash:
  {Q.filter("- mine\nok two\n") == "- mine\nok two" : String}

# LAW: output with no report is untouched
law filter_untouched:
  {Q.filter("ok one\nok two\n") == "ok one\nok two" : String}

# LAW: a trailing newline is not a difference
law chomp_trailing:
  {Q.chomp("a\nb\n\n\n") == "a\nb" : String}

# LAW: a blank line inside the output stays
law chomp_keeps_inner_blank:
  {Q.chomp("a\n\nb\n") == "a\n\nb" : String}

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

# LAW: the trailer is the lines after each `#|`
law trailer_extracts:
  {G.trailer(source()) == "ok one\nok two" : String}

# LAW: a file with no trailer wants nothing
law trailer_empty:
  {G.trailer("def main():\n  0\n") == "" : String}

# LAW: a comment that is not a trailer is not one
law trailer_ignores_note:
  {G.trailer("# a note\n#|ok\n") == "ok" : String}

# drift: the ledger against the import lines

# LAW: a line that is not a hub import names no package
law hash_of_local:
  for +s: String
  for e: {False{} == String.starts_with(s, "import 0x") : Bool}
  {D.hash_of(s) == "" : String}

# LAW: an import line names its package
law hash_of_import:
  {D.hash_of("import 0xaaaa/sha256.bend as S") == "0xaaaa" : String}

# LAW: a local import names none
law hash_of_relative:
  {D.hash_of("import ./run.bend as R") == "" : String}

# LAW: the same package imported twice counts once
law imported_dedups:
  {D.imported(["import 0xaaaa/a.bend as A", "import 0xaaaa/b.bend as B"])
    == ["0xaaaa"] : List<&2, String>}

# LAW: a ledger the source agrees with has no drift
law report_agrees:
  {D.report(["import 0xaaaa/s.bend as S", "import 0xbbbb/w.bend as W"],
    M.parse(ledger())) == [] : List<&2, String>}

# LAW: a hash the ledger does not name is drift, and so is a ledger entry
# nobody imports
law report_both_ways:
  {D.report(["import 0xaaaa/s.bend as S", "import 0xcccc/x.bend as X"],
    M.parse(ledger()))
    == ["drift: 0xcccc is imported but ez.toml does not name it",
      "drift: wire = 0xbbbb is in ez.toml but no import line uses it"]
    : List<&2, String>}

# LAW: a ledger entry nobody imports is drift
law report_unused:
  {D.report(["import 0xaaaa/s.bend as S"], M.parse(ledger()))
    == ["drift: wire = 0xbbbb is in ez.toml but no import line uses it"]
    : List<&2, String>}

# gate: the shadow's paths, and the run cut back up

# LAW: a path that does not open with `./` is already relative
law rel_plain:
  for +p: String
  for e: {False{} == String.starts_with(p, "./") : Bool}
  {G.rel(p) == p : String}

# LAW: a path find printed with `./` drops those two characters
law rel_dot:
  for +rest: String
  {G.rel("./" ++ rest) == rest : String}

# LAW: the shadow's root is the repo's root
law at_root:
  {G.at("") == G.root() : String}

# LAW: a directory of the shadow sits under the root
law at_under:
  for +d: String
  for e: {False{} == String.is_empty(d) : Bool}
  {G.at(d) == G.root() ++ "/" ++ d : String}

# LAW: a test names the project it is of
law proj_one:
  {G.proj("./ez/tests/drift.bend") == "ez" : String}

# LAW: a top-level test is of no project
law proj_top:
  {G.proj("./tests/cli.bend") == "" : String}

# LAW: a project deeper than one directory keeps its path
law proj_deep:
  {G.proj("a/b/tests/x.bend") == "a/b" : String}

# LAW: a project's aggregate sits under the project's own place
law src_place:
  {G.src("hub", "all") == ".ez/gate/hub/ez.gate/all.bend" : String}

# LAW: the shadow carves out every project and every level above it
law levels_of_two:
  {G.levels(["a/b", "hub"]) == ["", "a", "a/b", "hub"] : List<&2, String>}

# LAW: a directory holding no aggregate is reached with one link
law linked_keeps_bin:
  {G.linked(["./bin", "./hub", "./a"], ["a/b", "hub"]) == ["./bin"]
    : List<&2, String>}

# LAW: the aggregate reaches its tests without naming the project
law agg_imports_local:
  {String.contains(agg(), "import ../tests/two.bend as T2") == True{} : Bool}

# LAW: every test's main is called behind its own marker
law agg_calls_behind_mark:
  {String.contains(agg(),
    "IO.print(\"" ++ G.mark() ++ "./ez/tests/two.bend\")\n    T2.main()")
    == True{} : Bool}

# LAW: a test is given the lines behind its own marker
law slice_first:
  {G.slice(output(), "./ez/tests/one.bend") == "ok one\nok two" : String}

# LAW: the last test is given the lines up to the end
law slice_last:
  {G.slice(output(), "./ez/tests/two.bend") == "ok three" : String}

# LAW: a test the run never reached is given nothing
law slice_miss:
  {G.slice(output(), "./ez/tests/three.bend") == "" : String}

# LAW: a run that printed a marker started
law started_yes:
  {G.started(output()) == True{} : Bool}

# LAW: a run that printed none did not
law started_no:
  {G.started("error: unbound variable") == False{} : Bool}

# LAW: a header is read where a header sits
law headed_line:
  {G.headed("import Base\n# lanes: native\n", "# lanes: native") == True{}
    : Bool}

# LAW: and not where a string literal merely quotes one
law headed_quoted:
  {G.headed("def h() -> String:\n  \"# lanes: native\"\n", "# lanes: native")
    == False{} : Bool}

# LAW: a test that calls the argument reader is kept out of one
law solitary_reads_args:
  {G.solitary("def main() -> IO(Unit):\n  IO.args()\n") == True{} : Bool}

# LAW: a test whose comment only mentions it is not
law solitary_comment_only:
  {G.solitary("# this one never reads IO.args\ndef main() -> U32:\n  1\n")
    == False{} : Bool}

# clock: whether a budget is being kept, and the deadline the run
# effect holds. `date` and `test` are not among them.

# LAW: a budget of seconds is one that is being kept
law on_budget:
  {Clock.on("300") == True{} : Bool}

# LAW: zero turns it off
law on_zero:
  {Clock.on("0") == False{} : Bool}

# LAW: and so does nothing at all
law on_empty:
  {Clock.on("") == False{} : Bool}

# LAW: the deadline the run effect keeps is the absolute second
law by_effect_keeps:
  for +d: String
  for e: {False{} == String.is_empty(d) : Bool}
  {Clock.by.effect(d) == d : String}

# LAW: and no budget is a deadline of zero
law by_effect_empty:
  {Clock.by.effect("") == "0" : String}

# the command line as parse sees it, and the words `run` forwards

# LAW: an empty line has no tail
law rest_empty:
  {Args.rest([]) == [] : List<&2, String>}

# LAW: the tail is every word after the first
law rest_tail:
  {Args.rest(["run", "a", "b"]) == ["a", "b"] : List<&2, String>}

# LAW: a `run` line is parsed as the command alone
law argv_of_run:
  {Args.argv.of(["run", "x", "--flag"]) == ["run"] : List<&2, String>}

# LAW: every other line is parsed as it arrived
law argv_of_other:
  {Args.argv.of(["test", "--full"]) == ["test", "--full"] : List<&2, String>}

# LAW: an empty line stays empty
law argv_of_empty:
  {Args.argv.of([]) == [] : List<&2, String>}

# LAW: `tool run` is parsed as the command and its target. The words after
# the target are not flags of ez.
law argv_of_tool:
  {Args.argv.of(["tool", "run", "Emerging-Patterns/bolt", "--", "a"])
    == ["tool", "run", "Emerging-Patterns/bolt"] : List<&2, String>}

# LAW: `tool run` with no target is left that way, so the parse can say so
law argv_of_tool_bare:
  {Args.argv.of(["tool", "run"]) == ["tool", "run"] : List<&2, String>}

# LAW: a leading `--` is not a word the program was given
law tool_rest_dashes:
  {Args.tool.rest(["tool", "run", "Emerging-Patterns/bolt", "--", "a", "--b"])
    == ["a", "--b"] : List<&2, String>}

# LAW: words after the target are forwarded when no separator was written
law tool_rest_plain:
  {Args.tool.rest(["tool", "run", "o/r", "a"]) == ["a"] : List<&2, String>}

# LAW: `owner/repo` is that repository on GitHub, cached under the same path
law target_github:
  {Tgt.show(Tgt.classify("Emerging-Patterns/bolt"))
    == "remote https://github.com/Emerging-Patterns/bolt github.com/Emerging-Patterns/bolt"
    : String}

# LAW: a URL is kept, and `.git` is not part of its cache directory
law target_url:
  {Tgt.show(Tgt.classify("https://github.com/Emerging-Patterns/bolt.git"))
    == "remote https://github.com/Emerging-Patterns/bolt.git github.com/Emerging-Patterns/bolt"
    : String}

# LAW: `git@host:path` is a URL, cached as host/path
law target_scp:
  {Tgt.show(Tgt.classify("git@github.com:Emerging-Patterns/bolt.git"))
    == "remote git@github.com:Emerging-Patterns/bolt.git github.com/Emerging-Patterns/bolt"
    : String}

# LAW: a path that says it is a path is a path
law target_abs:
  {Tgt.show(Tgt.classify("/tmp/bolt")) == "local /tmp/bolt" : String}

# LAW: a relative path with a dot in it is a path, not a repository
law target_file:
  {Tgt.show(Tgt.classify("src/main.bend")) == "local src/main.bend" : String}

# LAW: an explicit relative path is a path even when it has two plain segments
law target_dot:
  {Tgt.show(Tgt.classify("./Emerging-Patterns/bolt"))
    == "local ./Emerging-Patterns/bolt" : String}

# LAW: nothing was asked for
law target_empty:
  {Tgt.show(Tgt.classify("")) == "bad a target is needed" : String}

# LAW: a slug that would leave the cache is refused
law target_escapes:
  {Tgt.show(Tgt.classify("https://example.com/../../tmp"))
    == "bad not a repository" : String}

# LAW: `~/…` expands under the home directory
law expand_tilde:
  {Tgt.expand("/home/u", "~/bolt") == "/home/u/bolt" : String}

# LAW: a path that is not a tilde is unchanged
law expand_plain:
  {Tgt.expand("/home/u", "/tmp/bolt") == "/tmp/bolt" : String}

# LAW: `bin` is the file that is built
law file_bin:
  {Tgt.file.of("ez/main.bend", "manifest/manifest.bend") == "ez/main.bend"
    : String}

# LAW: with no `bin`, the entry is built
law file_entry:
  {Tgt.file.of("", "bolt/main.bend") == "bolt/main.bend" : String}

# LAW: with neither, the file is `main.bend`
law file_default:
  {Tgt.file.of("", "") == "main.bend" : String}

# LAW: a package with no name builds `app`
law out_name_empty:
  {Tgt.out.name("") == "app" : String}

# LAW: otherwise the binary is the package's name
law out_name:
  {Tgt.out.name("bolt") == "bolt" : String}

# what a long step says. The words are the whole of the contract: a fetch, a
# cache hit, a drift and a missing manifest each have to be readable as that.

# LAW: a git package is named, and the repo it is fetched from is named
law dep_git_names_the_repo:
  {Say.dep.git("sha256", "https://github.com/Giulio2002/bend-sha256")
    == "dep sha256: git fetch (https://github.com/Giulio2002/bend-sha256)"
    : String}

# LAW: a hub package says it is fetching from the hub
law dep_hub_names_the_hash:
  {Say.dep.hub("0x0a5c2c95283e42e081da247c84debe18")
    == "dep 0x0a5c2c95283e42e081da247c84debe18: hub fetch" : String}

# LAW: a tree already on disk says so, and does not claim a fetch
law dep_cached_is_not_a_fetch:
  {Say.dep.cached("sha256") == "dep sha256: cached" : String}

# LAW: an entry file is the package's name
law label_from_entry:
  {Say.label("0xabc", "sha256.bend") == "sha256" : String}

# LAW: an entry with no name leaves the hash
law label_falls_back_to_hash:
  {Say.label("0xabc", "") == "0xabc" : String}

# LAW: a commit is shown by its first twelve characters
law brief_is_twelve:
  {Say.brief("3424b39197335f0aa741e8928dbe5c27b3bde0ef") == "3424b3919733"
    : String}

# LAW: a name shorter than that is left whole
law brief_keeps_short:
  {Say.brief("abc") == "abc" : String}

# LAW: a tool checkout is named with the commit it is fetching
law fetching_names_the_commit:
  {Say.fetching("github.com/Emerging-Patterns/bolt",
      "3424b39197335f0aa741e8928dbe5c27b3bde0ef")
    == "fetching github.com/Emerging-Patterns/bolt@3424b3919733" : String}

# LAW: an install says what was linked, and where
law installed_names_the_link:
  {Say.installed("bolt", "/home/u/.local/bin/bolt")
    == "installed bolt -> /home/u/.local/bin/bolt" : String}

# LAW: a pts device is a terminal
law tty_pts:
  {Say.tty.at("/dev/pts/3") == True{} : Bool}

# LAW: a pipe is not
law tty_pipe:
  {Say.tty.at("pipe:[12]") == False{} : Bool}

# LAW: stderr's terminal wins
law tty_prefers_stderr:
  {Say.tty.pick("/dev/pts/1", "pipe:[2]") == "/dev/pts/1" : String}

# LAW: stdout's terminal is used when stderr is a pipe
law tty_falls_back_to_stdout:
  {Say.tty.pick("pipe:[1]", "/dev/pts/4") == "/dev/pts/4" : String}

# LAW: neither being a terminal means no spinner
law tty_neither:
  {Say.tty.pick("pipe:[1]", "/dev/null") == "" : String}

# LAW: a manifest 404 names the package, that the hub has no manifest, and
# what to do next
law hub_404_teaches:
  {Say.hub.explain("0x0a5c2c95283e42e081da247c84debe18",
      "https://hub.bend-lang.com/0x0a5c2c95283e42e081da247c84debe18/manifest",
      "https://hub.bend-lang.com/0x0a5c2c95283e42e081da247c84debe18/manifest: the server answered 404")
    == "ez: 0x0a5c2c95283e42e081da247c84debe18: the hub has no manifest for this package (https://hub.bend-lang.com/0x0a5c2c95283e42e081da247c84debe18/manifest answered 404). Re-lock with `ez lock`, fix the dependency, or vendor it offline (`ez add`)."
    : String}

# LAW: a miss that is not a missing manifest keeps the reason it arrived with
law hub_other_miss_kept:
  {Say.hub.explain("0xabc", "https://hub.bend-lang.com/0xabc/manifest",
      "https://hub.bend-lang.com/0xabc/manifest does not hash to what was asked for")
    == "ez: https://hub.bend-lang.com/0xabc/manifest does not hash to what was asked for"
    : String}

# LAW: a drifted tag says the tree hash moved and that upgrade will not rewrite it
law drift_names_the_tag:
  {Say.drift("shake", "v0.1.0", "3424b39197335f0aa741e8928dbe5c27b3bde0ef",
      "0xebdf72b20ad527103f6efc0d2aa8f1ec", "0x97f80841000000000000000000000000")
    == "ez: shake: the tree hash of tagged commit v0.1.0 (3424b39197335f0aa741e8928dbe5c27b3bde0ef) no longer matches the pin (the package moved, or the hash is wrong: 0xebdf72b20ad527103f6efc0d2aa8f1ec on the pin, 0x97f80841000000000000000000000000 in the tree). `ez lock --upgrade` cannot fix a drifted pin. Update the dependency hash, re-add the package, or check the tag."
    : String}

# LAW: a ledger that names a tool section has tools
law tools_section_is_tools:
  {Say.has.tools("[package]\nname = \"ez\"\n\n[tools.bolt]\ngit = \"https://github.com/Emerging-Patterns/bolt\"\n")
    == True{} : Bool}

# LAW: a ledger of dependencies alone does not
law deps_are_not_tools:
  {Say.has.tools("[package]\nname = \"ez\"\n\n[deps.sha256]\nhash = \"0xabc\"\n")
    == False{} : Bool}

# LAW: `ez sync` in a project that pins tools is `ez tool sync`
law hint_sync_when_tools:
  {Say.hint(True{}) == "hint: `sync` is not a command; use `ez tool sync`"
    : String}

# LAW: without tools, the hint is lock or install
law hint_sync_without_tools:
  {Say.hint(False{})
    == "hint: `sync` is not a command. Use `ez lock` to resolve dependencies, or `ez tool install <target>` to link a binary."
    : String}
