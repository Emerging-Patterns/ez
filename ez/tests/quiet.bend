# ez: bend's check report dropped from a run's output, in both its wordings
import Base
import ../quiet.bend as Q
import ../../check/kit.bend as Check

# what 2.0.16 prints around a program's output
def old() -> String:
  "ok one\nAll terms check, with 3 unsafe annotations.\nok two\n"

# what 2.0.18 prints: the report, then a line per unsafe def
def new() -> String:
  "ok one\nAll terms check, but 2 defs rely on unsafe or foreign code:\n" ++
  "- ezrun.exec\n- Sha.hex\nok two\n"

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("the 2.0.16 report goes", Q.filter(old()), "ok one\nok two")
    Check.eq_str("the 2.0.18 report and its list go", Q.filter(new()), "ok one\nok two")
    Check.eq_str("a program's own dash line survives",
      Q.filter("- mine\nok two\n"), "- mine\nok two")
    Check.eq_str("output with no report is untouched",
      Q.filter("ok one\nok two\n"), "ok one\nok two")
    Check.eq_str("a trailing newline is not a difference", Q.chomp("a\nb\n\n\n"), "a\nb")
    Check.eq_str("a blank line inside the output stays", Q.chomp("a\n\nb\n"), "a\n\nb")
    Check.eq_str("nothing printed is nothing", Q.filter(""), "")

#|ok the 2.0.16 report goes
#|ok the 2.0.18 report and its list go
#|ok a program's own dash line survives
#|ok output with no report is untouched
#|ok a trailing newline is not a difference
#|ok a blank line inside the output stays
#|ok nothing printed is nothing
