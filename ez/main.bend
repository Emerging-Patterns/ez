# ez: the one binary. Its first argument is the subcommand and the rest are
# that subcommand's, read straight off the command line with `IO.args()`.
# Build it native (`bend ez/main.bend -o bin/ez.bin`); interpreted, bend's own
# CLI would take the flags meant for ez.
import Base
import ./args.bend as Args
import ./cmd.bend as Cmd
import ./test.bend as Test
import ./doctor.bend as Doctor
import ./env.bend as Env

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
  CPublish{}
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
  "  ez publish                      send the entry to the hub, under ez's " ++
  "0x name\n" ++
  "  ez test [--js-only] [--full]    run every */tests/*.bend, on both lanes\n" ++
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
                  Bool.pick(Sub, String.eq(name, "publish"), CPublish{},
                    Bool.pick(Sub, String.eq(name, "test"), CTest{},
                      Bool.pick(Sub, String.eq(name, "doctor"), CDoctor{},
                        Bool.pick(Sub, Bool.or(String.eq(name, "help"),
                          String.is_empty(name)),
                          CHelp{}, CUnknown{name}))))))))))))

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
    case CPublish{}:
      Cmd.publish()
    case CTest{}:
      Test.run(as)
    case CDoctor{}:
      Doctor.run()
    case CHelp{}:
      IO.write(usage())
    case CUnknown{name}:
      IO.die(Unit, 1, "ez: no such command: " ++ name)

# the command line taken apart: the subcommand, then its own arguments
def go(line: String & List<&2, String>) -> IO(Unit):
  (name, as) = line
  dispatch(command(name), as)

def main() -> IO(Unit):
  do IO<Unit>:
    Env.make()
    as : List<&2, String> <- Args.all()
    go(Args.split(as))
