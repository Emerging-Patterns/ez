import Base
import ../src/io/file.bend as FFile

# LAW: a file that would not open is nothing. The miss is None, not an empty
# body, so a path that is not there is told apart from a file that holds "".
law read_miss:
  for e: U32 & String
  {FFile.read.opened(Fail{e}) == IO.pure(Maybe<&2, String>, None{})
    : IO(Maybe<&2, String>)}
