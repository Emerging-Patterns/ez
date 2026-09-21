# `bin/ez.bin` is the program the end-to-end tests beside this one drive, and
# nothing in the gate builds it. A binary older than the sources it was built
# from answers for a program nobody is reading, and then every assertion those
# tests make is made against the wrong ez: the run goes green on a fix that is
# not in it, or red on a bug that was taken out an hour ago. Neither is a
# result, and both look exactly like a source bug.
#
# So the gate says so, here, once, as a test with a name. This is a test rather
# than a refusal in the runner because `ez test` runs in other people's
# projects too, where there is no `bin/ez.bin` to be stale and nothing to
# refuse; and it does not rebuild, because a gate that built the program it is
# about to grade would be grading its own work.
#
# A source is not the only thing a binary can be behind. The second test here
# is about the toolchain, and it exists because mtimes alone missed a real
# incident: bend 2.0.21 shipped mid-session, a branch stopped building under
# it, and the gate reported a pass. Nothing about that run was subtle. `bend`
# upgrading does not touch a single `.bend` file, so no source was newer than
# the binary; the build that would have caught it failed, and a `bend -o out`
# that fails writes no output and leaves the binary that is already there
# alone, with its old mtime intact. The mtime test therefore passes on exactly
# the run that has no new binary at all, and the end-to-end tests went on
# driving a binary the current toolchain had just stopped being able to
# produce. Reading the status of that build would have caught it, but the gate
# is not what runs it: `bend` is run by hand, or by a `nix build`, and by the
# time the tests start the only evidence left is what is on disk.
#
# So the toolchain is written down. `ez/cache.bend` already has the right
# notion of one — `bend version` and `$CC`, because a new bend checks and emits
# differently and the native lane hands its C to whatever `$CC` names — and
# this uses that same `tool()` rather than inventing a second answer to the
# same question. It is recorded under `.ez/`, beside the lane answers that are
# keyed on the very same string, because `.ez/` is the one directory this
# project keeps its own working state in and a second dot-directory at the root
# would be one more thing to explain, gitignore and clean.
#
# The rule that makes a stamp mean something: it is rewritten only when the
# binary is newer than the stamp itself, which is to say only when somebody
# built one since the last time this ran. Rewriting it on every run would erase
# the disagreement it exists to hold, and a gate that goes green the second
# time you run it is worse than one that never went red. A run that finds a
# toolchain other than the recorded one and no new binary fails, and keeps
# failing, until a build answers it.
#
# Two things this deliberately does not claim. A binary newer than the stamp is
# taken to have been built by the toolchain that is here now, which nothing on
# disk can prove — it is the same trust the mtime test already extends to a
# binary newer than its sources, and the alternative is the rebuild this file
# will not do. And the identity is `bend version`'s own words, so a `bend` that
# changes what it prints without changing what it compiles reads here as a
# changed toolchain. That is a false alarm whose remedy is one rebuild, and it
# is the direction to be wrong in: this test is allowed to ask for a build that
# was not needed, and is not allowed to pass a binary from a toolchain that is
# gone.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../ez/cache.bend as C
import ../check/kit.bend as Check

# every source the binary is compiled from that is newer than the binary.
# `check` and the `tests` directories are left out because `ez/main.bend` does
# not reach them: they are what grades ez, not what ez is made of. A missing
# binary is caught by the same walk, since `find` has nothing to compare against
# and says so.
def newer() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["find", ".", "-name", "*.bend",
      "-newer", "bin/ez.bin",
      "-not", "-path", "./.ez/*", "-not", "-path", "./.git/*",
      "-not", "-path", "./.claude/*", "-not", "-path", "./check/*",
      "-not", "-path", "*/tests/*"])
    return String.trim(R.text(out))

# where the toolchain that built the binary is remembered
def stamp() -> String:
  ".ez/built"

# whether the binary is newer than the stamp, as `find` answers it: the path
# back when it is, nothing when it is not. Whether the stamp is there at all is
# not asked here, because `find` answers a missing one with an error on the
# same pipe, and an error read as a file being newer is an answer arrived at by
# accident.
def since() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["find", "bin/ez.bin", "-newer", stamp()])
    return String.trim(R.text(out))

# whether the binary on disk is one the stamp has nothing to say about: either
# somebody built it since the stamp was written, or there is no stamp. A stamp
# that is not there at all counts, and so does an empty one, because the first
# run after this test was added has nothing to disagree with and there is no
# reading of the disk that makes a disagreement up. That run records what is
# here now, and the run after it is the one with something to say.
def built(+said: String, +out: String) -> Bool:
  Bool.or(String.is_empty(said), Bool.not(String.is_empty(out)))

# the toolchain the binary on disk was built by: the one that is here now when
# it was built since the stamp, and otherwise the one the stamp remembers.
def was(built: Bool, +now: String, +said: String) -> String:
  Bool.pick(String, built, now, said)

# the stamp brought up to date, for a binary that was built since it was
# written and for no other. `.ez/` is made first because this test is the only
# thing that writes there in a checkout that has not run a subcommand yet, and
# Base has no mkdir.
def keep(built: Bool, +now: String) -> IO(Unit):
  match built:
    case True{}:
      do IO<Unit>:
        _mk : String <- R.exec(["mkdir", "-p", ".ez"])
        _w : Bool <- F.write(stamp(), now ++ "\n")
        return Unit{}
    case False{}:
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    +stale : String <- newer()
    Check.eq_str("bin/ez.bin is newer than every source it is built from",
      stale, "")
    +now : String <- C.tool()
    +out : String <- since()
    m : Maybe<&2, String> <- F.read(stamp())
    +said : String <- IO.pure(String, String.trim(F.text_of(m)))
    +fresh : Bool <- IO.pure(Bool, built(said, out))
    Check.eq_str("bin/ez.bin was built by the toolchain that is here now",
      was(fresh, now, said), now)
    keep(fresh, now)

#|ok bin/ez.bin is newer than every source it is built from
#|ok bin/ez.bin was built by the toolchain that is here now
