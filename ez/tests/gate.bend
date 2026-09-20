# ez: the one binary a project is compiled as, and the run cut back up into the
# test that printed each part of it
import Base
import ../gate.bend as G
import ../../check/kit.bend as Check

# the name of the call that keeps a test out of an aggregate, spelled in two
# halves. Written whole it would sit on a line of this file that is not a
# comment, and `solitary` would then hold this very test solitary — which is
# the limit the comment on it admits to, demonstrated rather than argued.
def reader() -> String:
  "IO." ++ "args"

# a claim, as a word a comparison can be made of
def shown(b: Bool) -> String:
  Bool.pick(String, b, "yes", "no")

# what an aggregate of two tests prints: each test's output behind its marker
def output() -> String:
  G.mark() ++ "./ez/tests/one.bend\nok one\nok two\n" ++
    G.mark() ++ "./ez/tests/two.bend\nok three"

# two tests of one project, as one program
def source() -> String:
  G.agg("ez", ["./ez/tests/one.bend", "./ez/tests/two.bend"])

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a test names the project it is of",
      G.proj("./ez/tests/drift.bend"), "ez")
    Check.eq_str("a top-level test is of no project",
      G.proj("./tests/cli.bend"), "")
    Check.eq_str("a project deeper than one directory keeps its path",
      G.proj("a/b/tests/x.bend"), "a/b")
    Check.eq_str("the aggregate reaches its tests without naming the project",
      shown(String.contains(source(), "import ../tests/two.bend as T2")), "yes")
    Check.eq_str("a project's aggregate sits under the project's own place",
      G.src("hub", "all"), ".ez/gate/hub/ez.gate/all.bend")
    Check.eq_str("the shadow's root is the repo's root",
      G.at(""), ".ez/gate")
    Check.eq_str("the shadow carves out every project and every level above it",
      String.join(G.levels(["a/b", "hub"]), " "), " a a/b hub")
    Check.eq_str("a directory holding no aggregate is reached with one link",
      String.join(G.linked(["./bin", "./hub", "./a"], ["a/b", "hub"]), " "),
      "./bin")
    Check.eq_str("every test's main is called behind its own marker",
      shown(String.contains(source(),
        "IO.print(\"" ++ G.mark() ++ "./ez/tests/two.bend\")\n    T2.main()")),
      "yes")
    Check.eq_str("a test is given the lines behind its own marker",
      G.slice(output(), "./ez/tests/one.bend"), "ok one\nok two")
    Check.eq_str("the last test is given the lines up to the end",
      G.slice(output(), "./ez/tests/two.bend"), "ok three")
    Check.eq_str("a test the run never reached is given nothing",
      G.slice(output(), "./ez/tests/three.bend"), "")
    Check.eq_str("a run that printed a marker started",
      shown(G.started(output())), "yes")
    Check.eq_str("a run that printed none did not",
      shown(G.started("error: unbound variable")), "no")
    Check.eq_str("a header is read where a header sits",
      shown(G.headed("import Base\n# lanes: native\n", "# lanes: native")),
      "yes")
    Check.eq_str("and not where a string literal merely quotes one",
      shown(G.headed("def h() -> String:\n  \"# lanes: native\"\n",
        "# lanes: native")), "no")
    Check.eq_str("a test that calls the argument reader is kept out of one",
      shown(G.solitary("def main() -> IO(Unit):\n  " ++ reader() ++ "()\n")),
      "yes")
    Check.eq_str("a test whose comment only mentions it is not",
      shown(G.solitary("# this one never reads " ++ reader() ++
        "\ndef main() -> U32:\n  1\n")), "no")

#|ok a test names the project it is of
#|ok a top-level test is of no project
#|ok a project deeper than one directory keeps its path
#|ok the aggregate reaches its tests without naming the project
#|ok a project's aggregate sits under the project's own place
#|ok the shadow's root is the repo's root
#|ok the shadow carves out every project and every level above it
#|ok a directory holding no aggregate is reached with one link
#|ok every test's main is called behind its own marker
#|ok a test is given the lines behind its own marker
#|ok the last test is given the lines up to the end
#|ok a test the run never reached is given nothing
#|ok a run that printed a marker started
#|ok a run that printed none did not
#|ok a header is read where a header sits
#|ok and not where a string literal merely quotes one
#|ok a test that calls the argument reader is kept out of one
#|ok a test whose comment only mentions it is not
