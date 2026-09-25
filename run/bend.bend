# run/bend: which bend is on the PATH, asked the way that bend will answer.
#
# bend has had the question two ways round. Up to 2.0.16 it is `bend --version`
# and `bend version` is "no such file: version"; from 2.0.18 on it is `bend
# version` and the flag is "unknown option --version". Either way the spelling
# it does not know exits non-zero, which looks exactly like a bend that is not
# installed — so a caller that asks only one way cannot tell a missing bend
# from an old one, and ez has two callers that need the banner: doctor's
# report and the toolchain part of a cache key.
# Asking both ways, current spelling first, is the whole of this module.
import Base
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R

# the older spelling, tried only when the current one was not understood
def version.older(ok: Bool, out: String) -> IO(String):
  match ok:
    case True{}:
      IO.pure(String, out)
    case False{}:
      R.exec(["bend", "--version"])

# `bend` asked which bend it is, as a run's answer: the status line, then the
# banner. A bend that is not on the PATH fails both spellings, so the status
# an absent bend answers with is still the one the caller sees.
def version() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["bend", "version"])
    version.older(R.ok(out), out)
