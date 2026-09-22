# ez: the laws. The human states them; PROOF.bend must prove them. The string
# and path facts a test run turns on live here: what bend's own chatter is,
# what a `#|` trailer asks for, which `0x` name an import line wrote, and
# where a test sits in the shadow. The clock's by.effect deadline lives
# here too, and the command line as parse sees it. The OS half of the clock
# is not among them.
import Base
import ./quiet.bend as Q
import ./drift.bend as D
import ./gate.bend as G
import ./clock.bend as Clock
import ./args.bend as Args
import ./target.bend as Tgt
import ../manifest/manifest.bend as M

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

# gate: the shadow's paths

# LAW: a path that does not open with `./` is already relative
law rel_plain:
  for +p: String
  for e: {False{} == String.starts_with(p, "./") : Bool}
  {G.rel(p) == p : String}

# LAW: a path find printed with `./` drops those two characters
law rel_dot:
  for +rest: String
  {G.rel("./" ++ rest) == rest : String}

# LAW: a directory of the shadow sits under the root
law at_under:
  for +d: String
  for e: {False{} == String.is_empty(d) : Bool}
  {G.at(d) == G.root() ++ "/" ++ d : String}

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

# LAW: `owner/repo` is that repository on GitHub, cached under the same path
# toward EZ-RES-3
law target_github:
  {Tgt.show(Tgt.classify("Emerging-Patterns/bolt"))
    == "remote https://github.com/Emerging-Patterns/bolt github.com/Emerging-Patterns/bolt"
    : String}

# LAW: a URL is kept, and `.git` is not part of its cache directory
# toward EZ-RES-3
law target_url:
  {Tgt.show(Tgt.classify("https://github.com/Emerging-Patterns/bolt.git"))
    == "remote https://github.com/Emerging-Patterns/bolt.git github.com/Emerging-Patterns/bolt"
    : String}

# LAW: `git@host:path` is a URL, cached as host/path
# toward EZ-RES-3
law target_scp:
  {Tgt.show(Tgt.classify("git@github.com:Emerging-Patterns/bolt.git"))
    == "remote git@github.com:Emerging-Patterns/bolt.git github.com/Emerging-Patterns/bolt"
    : String}

# LAW: a path that says it is a path is a path
# toward EZ-RES-3
law target_abs:
  {Tgt.show(Tgt.classify("/tmp/bolt")) == "local /tmp/bolt" : String}

# LAW: a relative path with a dot in it is a path, not a repository
# toward EZ-RES-3
law target_file:
  {Tgt.show(Tgt.classify("src/main.bend")) == "local src/main.bend" : String}

# LAW: an explicit relative path is a path even when it has two plain segments
# toward EZ-RES-3
law target_dot:
  {Tgt.show(Tgt.classify("./Emerging-Patterns/bolt"))
    == "local ./Emerging-Patterns/bolt" : String}

# LAW: nothing was asked for
# toward EZ-RES-3
law target_empty:
  {Tgt.show(Tgt.classify("")) == "bad a target is needed" : String}

# LAW: a slug that would leave the cache is refused
# toward EZ-TOOL-8
law target_escapes:
  {Tgt.show(Tgt.classify("https://example.com/../../tmp"))
    == "bad not a repository" : String}

# LAW: `~/…` expands under the home directory
# toward EZ-RES-3
law expand_tilde:
  {Tgt.expand("/home/u", "~/bolt") == "/home/u/bolt" : String}

# LAW: a path that is not a tilde is unchanged
# toward EZ-RES-3
law expand_plain:
  {Tgt.expand("/home/u", "/tmp/bolt") == "/tmp/bolt" : String}

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
