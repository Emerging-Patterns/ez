# url: a url comes apart into the four things a GET needs
import Base
import ../url.bend as Url
import ../../check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a port named is the port used",
      Url.show(Url.parse("http://127.0.0.1:8080/x")), "http 127.0.0.1 8080 /x")
    Check.eq_str("a trailing slash is the root",
      Url.show(Url.parse("http://h/")), "http h 80 /")

#|ok a port named is the port used
#|ok a trailing slash is the root
