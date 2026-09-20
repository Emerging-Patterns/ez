# ez: the one binary a project is compiled as, and the run cut back up into the
# test that printed each part of it
import Base
import ../gate.bend as G
import ../../check/kit.bend as Check

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

#|ok a test names the project it is of
#|ok a top-level test is of no project
#|ok a project deeper than one directory keeps its path
#|ok the aggregate reaches its tests without naming the project
#|ok every test's main is called behind its own marker
#|ok a test is given the lines behind its own marker
#|ok the last test is given the lines up to the end
#|ok a test the run never reached is given nothing
#|ok a run that printed a marker started
#|ok a run that printed none did not
