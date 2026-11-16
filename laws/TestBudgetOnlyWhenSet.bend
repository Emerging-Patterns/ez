# `ez test` keeps a wall-clock budget exactly when one was given: an empty
# budget, or one of `0`, keeps none, and any other keeps one. This is
# internal: it fixes the choice ez/clock.bend makes for ez/test.bend.
import Base
import ../src/ez/clock.bend as Clock

# LAW: an empty budget keeps none
law off_when_empty:
  for +secs: String
  for e: {True{} == String.is_empty(secs) : Bool}
  {Clock.on(secs) == False{} : Bool}

# LAW: and a budget of `0` keeps none
law off_when_zero:
  for +secs: String
  for e: {True{} == String.eq(secs, "0") : Bool}
  {Clock.on(secs) == False{} : Bool}

# LAW: and any other budget is kept
law on_otherwise:
  for +secs: String
  for e0: {False{} == String.is_empty(secs) : Bool}
  for e1: {False{} == String.eq(secs, "0") : Bool}
  {Clock.on(secs) == True{} : Bool}
