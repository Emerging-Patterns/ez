# check/kit: the test kit. A test file states what it expects in its `#|`
# trailer, and the gate compares the run's output against those lines.
import Base

# the line a check prints, pass or fail
def say(ok: Bool, name: String, got: String, want: String) -> IO(Unit):  # noqa: L001 IO: prints a test verdict
  match ok:
    case True{}:
      IO.print("ok " ++ name)
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got ++ ", want " ++ want)

# passes when two strings are equal
def eq_str(name: String, +got: String, +want: String) -> IO(Unit):  # noqa: L001 IO: prints a test verdict
  say(String.eq(got, want), name, got, want)
