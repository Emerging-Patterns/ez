# ez/key: what a cached tool checkout and binary were made from. A checkout
# is its commit. A binary is not: a pin's `bin` or `entry` builds another file
# from the same commit, and another bend builds the same file differently. So
# the binary's record is all three, and it is reused only when every one of
# them is the one about to be built.
import Base

# the commit, the file handed to bend, and the bend that built it
type Key is Data:
  Key{rev: String, file: String, bend: String}

# the record that matches nothing: an empty commit is never reused
def none() -> Key:
  Key{"", "", ""}

# the record as it is written, one field to a line
def show(key: Key) -> String:
  match key:
    case Key{+r, +f, +b}:
      r ++ "\n" ++ f ++ "\n" ++ b ++ "\n"

# exactly three lines, or no record. A cache written before the file and the
# bend were recorded holds the commit alone, and that reads as no record.
def read.third(+rev: String, +file: String, ls: List<&2, String>) -> Key:
  match ls:
    case []:
      none()
    case +b <> t:
      match t:
        case []:
          Key{rev, file, b}
        case _h <> _t:
          none()

def read.second(+rev: String, ls: List<&2, String>) -> Key:
  match ls:
    case []:
      none()
    case +f <> t:
      read.third(rev, f, t)

def read.lines(ls: List<&2, String>) -> Key:
  match ls:
    case []:
      none()
    case +r <> t:
      read.second(r, t)

# a record's text, as `show` wrote it and a file read trimmed it
def read(+text: String) -> Key:
  read.lines(String.split(text, '\n'))

# the checkout is this commit, and there is a commit at all. The checkout's
# record is the commit alone: the file and the bend are the binary's business.
def checkout(+was: String, +now: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(now)), String.eq(was, now))

# the three fields the same, and a commit at all. An empty commit is a dirty
# tree or a directory that is not a checkout, and those are built every time.
def reuse(was: Key, now: Key) -> Bool:
  match was:
    case Key{+r0, +f0, +b0}:
      match now:
        case Key{+r1, +f1, +b1}:
          Bool.and(Bool.not(String.is_empty(r1)),
            Bool.and(String.eq(r0, r1),
              Bool.and(String.eq(f0, f1), String.eq(b0, b1))))
