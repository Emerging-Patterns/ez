# check/kit: the test kit. A test file states what it expects in its `#|`
# trailer, and the gate compares the run's output against those lines.
import Base

# the line a check prints, pass or fail
def say(ok: Bool, name: String, got: String, want: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok " ++ name)
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got ++ ", want " ++ want)

# passes when two strings are equal
def eq_str(name: String, +got: String, +want: String) -> IO(Unit):
  say(String.eq(got, want), name, got, want)

# passes when two U32 are equal
def eq_u32(name: String, got: U32, want: U32) -> IO(Unit):
  eq_str(name, U32.show(got), U32.show(want))
