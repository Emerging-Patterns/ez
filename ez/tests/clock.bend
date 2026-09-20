# ez/clock: the wall-clock budget a run has to finish inside. The deadline is
# worked out once by `date` and compared once by `test`, so what is checked
# here is that a second already gone by reads as over and one still to come
# does not.
import Base
import ../../ez/clock.bend as Clock
import ../../check/kit.bend as Check

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

def main() -> IO(Unit):
  do IO<Unit>:
    yes("a budget of seconds is one that is being kept", Clock.on("300"))
    yes("zero turns it off", Bool.not(Clock.on("0")))
    yes("and so does nothing at all", Bool.not(Clock.on("")))
    +none : String <- Clock.start("0")
    yes("a run with no budget gets no deadline", String.is_empty(none))
    +soon : String <- Clock.start("300")
    yes("a run with one gets a second to be finished by",
      Bool.not(String.is_empty(soon)))
    +late : Bool <- Clock.over(soon)
    yes("five minutes from now has not gone by", Bool.not(late))
    +past : Bool <- Clock.over("0")
    yes("the epoch has", past)
    +never : Bool <- Clock.over("")
    yes("and a run with no deadline is never over it", Bool.not(never))
    Check.eq_str("the deadline the run effect keeps is the absolute second",
      Clock.by.effect("1789930000"), "1789930000")
    Check.eq_str("and no budget is a deadline of zero", Clock.by.effect(""), "0")

#|ok a budget of seconds is one that is being kept
#|ok zero turns it off
#|ok and so does nothing at all
#|ok a run with no budget gets no deadline
#|ok a run with one gets a second to be finished by
#|ok five minutes from now has not gone by
#|ok the epoch has
#|ok and a run with no deadline is never over it
#|ok the deadline the run effect keeps is the absolute second
#|ok and no budget is a deadline of zero
