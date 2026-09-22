# pkg: what `bend <entry> --publish` would upload, printed rather than
# uploaded. The hash on the first line, the directory the file paths are
# written from on the second, then the manifest. The entry arrives in EZ_ENTRY,
# since a native Bend binary takes no arguments of its own.
#
#   EZ_ENTRY=src/lib.bend bend pkg/main.bend
import Base
import ./pkg.bend as K

# an environment variable's text; unset, ""
def text_of(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# a package on three or more lines
def show(+pkg: K.Pkg) -> String:
  K.pkg.hash(pkg) ++ "\n" ++ K.pkg.root(pkg) ++ "\n" ++ K.manifest_of(K.pkg.files(pkg))

# the package of an entry that was named
def report(+at: String) -> IO(Unit):
  do IO<Unit>:
    p : K.Pkg <- K.pkg_of(at)
    IO.write(show(p))

# nothing to weigh is an error, not an empty package
def go(+at: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(at),
    IO.die(Unit, 1, "usage: EZ_ENTRY=<entry.bend> bend pkg/main.bend"),
    report(at))

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("EZ_ENTRY")
    go(String.trim(text_of(r)))
