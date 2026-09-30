# ez/clock: the wall-clock budget a run has to finish inside.
#
# `ez test` is held to it, since a check nobody waits for is not one. The
# budget is a comparison like any other: it is checked, it is counted, and a run that
# overran fails on it the way a test that printed the wrong line fails. That is
# the difference between a number in a readme and a number something enforces.
#
# Base has no clock. `ez/when.bend` asks `date` for the deadline and `test`
# whether it has passed, so nothing here parses a number.
import Base
import ../share/env.bend as Env

# how many seconds a whole run may take. Five minutes is what the gate is held
# to; a tree that honestly needs longer says so in EZ_DEADLINE, and "0" turns
# the budget off for someone bisecting with the cache cold.
def seconds() -> IO(String):
  Env.var("EZ_DEADLINE", "300")

# whether a budget is being kept at all
def on(+secs: String) -> Bool:
  Bool.not(Bool.or(String.is_empty(secs), String.eq(secs, "0")))

# the deadline as the run effect wants it: an absolute second, or "0" when
# there is no budget to keep. The effect is what queues the jobs, so it is what
# keeps the deadline; a job bounded by what was left when its batch started is
# not bounded at all once it waits its turn behind three others.
def by.effect(+deadline: String) -> String:
  Bool.pick(String, String.is_empty(deadline), "0", deadline)
