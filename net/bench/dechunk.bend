# net/bench/dechunk: what a chunked body costs to put back together.
#
# This is not a test and the gate does not collect it. It lives in `bench/`
# rather than `tests/` on purpose: `ez test` runs every `*/tests/*.bend` on
# both lanes, and a body big enough to show the cost would add minutes to the
# gate to assert nothing the unit tests do not already assert.
#
#   bend net/bench/dechunk.bend -o /tmp/dechunk
#   /tmp/dechunk decode 512     # the decode, and the body building under it
#   /tmp/dechunk raw 512        # the body building alone, to subtract
#
# The body is `n` chunks of 8192 characters each, which is the shape a server
# hands back when it writes a package out a record at a time. `raw` prints the
# length of the encoded body and `decode` the length of what came back out of
# it, so a reviewer can see the decode happened and was not skipped.
#
# What it said when net/http.bend's decode was rewritten, on 512 chunks, which
# is a 4 MB body, built native:
#
#   raw 512                                           0.21 s
#   decode 512, before the rewrite                  154.47 s
#   decode 512, with only the accumulator lifted    133.96 s
#   decode 512, with only the picks made to stop     11.41 s
#   decode 512, after                                 0.40 s
#
# Two defects, each hiding the other's cost: the accumulator made the decode
# quadratic in the number of chunks, and the `Bool.pick` arms made every step
# of it walk the whole remaining body. Taking out either one alone leaves the
# other in charge. The decode itself, with the body building subtracted, went
# from 154.3 s to 0.19 s. `decode 2048`, a 16 MB body, takes 1.61 s: four
# times the body for four times the time, which is the linear cost the
# rewrite was for.
import Base
import ../http.bend as Http

# the payload of one chunk, and the hex its header states. 8192 is 0x2000.
def chunk.size() -> Nat:
  U32.to_nat(8192)

def chunk.head() -> String:
  "2000"

# one chunk on the wire: the length in hex, a CRLF, the bytes, a CRLF
def chunk() -> String:
  chunk.head() ++ "\r\n" ++ String.repeat("x", chunk.size()) ++ "\r\n"

# `n` of them, and then the zero chunk that ends the body
def body.go(n: Nat, +one: String) -> String:
  match n:
    case 0n:
      "0\r\n\r\n"
    case 1n+p:
      one ++ body.go(p, one)

# a chunked body of `n` chunks, built once so both modes frame the same bytes
def body(n: Nat) -> String:
  body.go(n, chunk())

# the answer a mode asks for, as the length of a string. Both modes build the
# same body, so the difference between the two timings is the decode alone.
def run.at(raw: Bool, n: Nat) -> String:
  match raw:
    case True{}:
      "encoded " ++ Nat.show(String.length(body(n)))
    case False{}:
      "decoded " ++ Nat.show(String.length(Http.dechunk(body(n))))

# the mode named on the command line, answered
def run(mode: String, n: Nat) -> String:
  run.at(String.eq(mode, "raw"), n)

# a &1 list copied into a &2 one, since `IO.args()` answers a list read once
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

# the nth argument, "" past the end
def at(xs: List<&2, String>, n: Nat) -> String:
  match xs n:
    case Nil{} 0n:
      ""
    case Nil{} 1n+p:
      ""
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      at(t, p)

# the command line: a mode, and how many chunks the body holds. 512 chunks of
# 8192 is a 4 MB body, which is a package of the size ez actually fetches.
def start(as: List<&2, String>) -> IO(Unit):
  match as:
    case Nil{}:
      IO.print(run("decode", U32.to_nat(512)))
    case Con{h, t}:
      IO.print(run(h,
        U32.to_nat(Maybe.default(&2, U32, U32.read(at(t, 0n)), 512))))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start(copy(xs))
