# fetch: the client against a real server. tests/fetch.sh stands one up, writes
# its port into .gate/netport, and runs this on both lanes. It is under tests/
# rather than net/tests/ because the gate runs net/tests/*.bend with nothing
# listening.
import Base
import ../net/client.bend as Client
import ../io/file.bend as File
import ../run/run.bend as R
import ../check/kit.bend as Check

# the port the server was given, without the newline it was written with
def port() -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- File.read(".gate/netport")
    +text : String <- IO.pure(String, File.text_of(m))
    return String.take(text, Nat.sub(String.length(text), 1n))

# a url on that server
def at(+port: String, path: String) -> String:
  "http://127.0.0.1:" ++ port ++ path

# a fetch's answer on one line, the status and the text
def show(+out: String) -> String:
  R.code(out) ++ " " ++ R.text(out)

def main() -> IO(Unit):
  do IO<Unit>:
    +p : String <- port()
    +plain : String <- Client.get(at(p, "/plain"))
    Check.eq_str("a Content-Length body comes back whole", show(plain),
      "0 a manifest line\n")
    +chunked : String <- Client.get(at(p, "/chunked"))
    Check.eq_str("a chunked body is put back together", show(chunked),
      "0 one two three four\n")
    +gone : String <- Client.get(at(p, "/gone"))
    Check.eq_str("a 404 is a status, never a body", show(gone),
      "22 the server answered 404")
    +shut : String <- Client.get("http://127.0.0.1:1/plain")
    Check.eq_str("a port with nothing on it names the host it could not reach",
      show(shut), "6 could not reach 127.0.0.1 port 1")
    +bad : String <- Client.get("nonsense")
    Check.eq_str("a url that is not one never reaches a socket", show(bad),
      "22 nonsense: has no //")

#|ok a Content-Length body comes back whole
#|ok a chunked body is put back together
#|ok a 404 is a status, never a body
#|ok a port with nothing on it names the host it could not reach
#|ok a url that is not one never reaches a socket
