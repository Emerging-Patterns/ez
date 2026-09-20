# fetch: the client against a real server. The server is check/framing.bend,
# started here on a port of this test's own and stopped again at the end, so
# the test is answered by the server it started and never by a stranger's.
#
# It is under tests/ rather than net/tests/ because it drives a socket, and the
# unit tests beside the code are about what can be said without one.
import Base
import ../net/client.bend as Client
import ../run/run.bend as R
import ../check/kit.bend as Check
import ../check/world.bend as W

# a url on that server
def at(+port: String, path: String) -> String:
  "http://127.0.0.1:" ++ port ++ path

# a fetch's answer on one line, the status and the text
def show(+out: String) -> String:
  R.code(out) ++ " " ++ R.text(out)

# every fetch, once the server is up
def fetch(+p: String) -> IO(Unit):
  do IO<Unit>:
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

# the server started, driven and stopped
def go(+here: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    +pid : String <- W.spawn(["env", "BEND_LIB=" ++ here ++ "/.ez/lib",
      "bend", here ++ "/check/framing.bend", port])
    up : Bool <- W.ready(["curl", "-fsS", "--max-time", "5",
      "http://127.0.0.1:" ++ port ++ "/"])
    Check.eq_str("the server answers",
      Bool.pick(String, up, "yes", "no"), "yes")
    fetch(port)
    W.stop(pid)

def main() -> IO(Unit):
  do IO<Unit>:
    here : String <- W.here()
    port : String <- W.port()
    go(here, port)

#|ok the server answers
#|ok a Content-Length body comes back whole
#|ok a chunked body is put back together
#|ok a 404 is a status, never a body
#|ok a port with nothing on it names the host it could not reach
#|ok a url that is not one never reaches a socket
