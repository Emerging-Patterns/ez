# ez: the one binary behind the `ez` script. EZ_CMD picks the subcommand and
# EZ_ARGS carries the rest, one a line, because a native Bend binary takes no
# arguments of its own. Build it native (`bend ez/main.bend -o bin/ez.bin`).
import Base
import ./args.bend as Args
import ./cmd.bend as Cmd
import ./test.bend as Test
import ./doctor.bend as Doctor

# a subcommand
type Sub is Data:
  CInit{}
  CAdd{}
  CRemove{}
  CLock{}
  CFetch{}
  CCheck{}
  CBuild{}
  CRun{}
  CTest{}
  CDoctor{}
  CHelp{}
  CUnknown{name: String}

# what `ez` prints when asked, and when it does not understand
def usage() -> String:
  "ez: dependency tracking and builds for Bend 2\n" ++
  "\n" ++
  "  ez init [name] [entry.bend]     write an ez.toml for a new project\n" ++
  "  ez add <url> <ref> <entry>      vendor a git package and record it\n" ++
  "  ez remove <name>                drop a package from the ledger\n" ++
  "  ez lock                         resolve every import, write ez.lock.toml\n" ++
  "  ez fetch                        fill BEND_LIB from the lock\n" ++
  "  ez check                        check the entry, without running it\n" ++
  "  ez build [out]                  build the entry to a native binary\n" ++
  "  ez run [args..]                 check and run the entry\n" ++
  "  ez test [--js-only]             run every */tests/*.bend, on both lanes\n" ++
  "  ez doctor                       report on the toolchain and the project\n"

# a subcommand by its name
def command(+name: String) -> Sub:
  Bool.pick(Sub, String.eq(name, "init"), CInit{},
    Bool.pick(Sub, String.eq(name, "add"), CAdd{},
      Bool.pick(Sub, String.eq(name, "remove"), CRemove{},
        Bool.pick(Sub, String.eq(name, "lock"), CLock{},
          Bool.pick(Sub, String.eq(name, "fetch"), CFetch{},
            Bool.pick(Sub, String.eq(name, "check"), CCheck{},
              Bool.pick(Sub, String.eq(name, "build"), CBuild{},
                Bool.pick(Sub, String.eq(name, "run"), CRun{},
                  Bool.pick(Sub, String.eq(name, "test"), CTest{},
                    Bool.pick(Sub, String.eq(name, "doctor"), CDoctor{},
                      Bool.pick(Sub, Bool.or(String.eq(name, "help"), String.is_empty(name)),
                        CHelp{}, CUnknown{name})))))))))))

# what a subcommand runs
def dispatch(sub: Sub, as: List<&2, String>) -> IO(Unit):
  match sub:
    case CInit{}:
      Cmd.init(as)
    case CAdd{}:
      Cmd.add(as)
    case CRemove{}:
      Cmd.remove(as)
    case CLock{}:
      Cmd.lock()
    case CFetch{}:
      Cmd.fetch()
    case CCheck{}:
      Cmd.check()
    case CBuild{}:
      Cmd.build(as)
    case CRun{}:
      Cmd.run(as)
    case CTest{}:
      Test.run(as)
    case CDoctor{}:
      Doctor.run()
    case CHelp{}:
      IO.write(usage())
    case CUnknown{name}:
      IO.die(Unit, 1, "ez: no such command: " ++ name)

def main() -> IO(Unit):
  do IO<Unit>:
    name : String <- Args.command()
    as : List<&2, String> <- Args.args()
    dispatch(command(name), as)
