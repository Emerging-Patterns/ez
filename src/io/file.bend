# io/file: a whole file read or written in one call. Base gives an open handle
# and chunked reads; this is the loop over them.
import Base

# the handle closed, and whatever was gathered
def slurp.end(file: File, acc: String) -> IO(String):
  do IO<String>:
    File.close(file)
    return acc

# an empty chunk means the end of the file
def slurp.cut(chunk: String, file: File, acc: String, rest: File -> String -> IO(String)) -> IO(String):
  match chunk:
    case SNil{}:
      slurp.end(file, acc)
    case SCon{c, t}:
      rest(file, acc ++ SCon{c, t})

# a failed read ends the file as surely as an empty one
def slurp.more(
  res: Result<&1, &1, U32 & String, String>,
  file: File,
  acc: String,
  rest: File -> String -> IO(String)
) -> IO(String):
  match res:
    case Fail{_e}:
      slurp.end(file, acc)
    case Done{chunk}:
      slurp.cut(chunk, file, acc, rest)

# the handle comes back paired with what it read
def slurp.next(
  got: File & Result<&1, &1, U32 & String, String>,
  acc: String,
  rest: File -> String -> IO(String)
) -> IO(String):
  (file, r) = got
  slurp.more(r, file, acc, rest)

# the whole file, read in chunks until one is empty, or the fuel is
def slurp(fuel: Nat, file: File, acc: String) -> IO(String):
  match fuel:
    case 0n:
      slurp.end(file, acc)
    case 1n+f:
      do IO<String>:
        got : File & Result<&1, &1, U32 & String, String> <- File.read(file, 65536)
        slurp.next(got, acc, fl => a => slurp(f, fl, a))

# what an opened file holds, or nothing when it would not open
def read.opened(res: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, String>):
  match res:
    case Fail{_e}:
      IO.pure(Maybe<&2, String>, None{})
    case Done{file}:
      do IO<Maybe<&2, String>>:
        text : String <- slurp(U32.to_nat(100000), file, "")
        return Some{text}

# a file's text, or None when it cannot be opened
def read(path: String) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    read.opened(r)

# whether a write reported success
def write.ok(res: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match res:
    case Fail{_e}:
      False{}
    case Done{_u}:
      True{}

# a write's outcome, once the handle is shut
def write.done(written: File & Result<&1, &1, U32 & String, Unit>) -> IO(Bool):
  (file, r) = written
  do IO<Bool>:
    File.close(file)
    return write.ok(r)

# the text written to an opened file
def write.opened(res: Result<&1, &1, U32 & String, File>, text: String) -> IO(Bool):
  match res:
    case Fail{_e}:
      IO.pure(Bool, False{})
    case Done{file}:
      do IO<Bool>:
        w : File & Result<&1, &1, U32 & String, Unit> <- File.write(file, text)
        write.done(w)

# a file replaced with this text; False when it could not be written
def write(path: String, text: String) -> IO(Bool):
  do IO<Bool>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    write.opened(r, text)

# a file's text, or "" when there is none
def text_of(got: Maybe<&2, String>) -> String:
  match got:
    case None{}:
      ""
    case Some{s}:
      s
