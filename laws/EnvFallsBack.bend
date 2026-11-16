# A variable ez reads with a default reads as its value when it holds one,
# and as the default when it is unset or empty. This is internal: it holds
# src/share/env.bend's fallback in place, under BEND_LIB and EZ_CAP.
import Base
import ../src/share/env.bend as Env

# LAW: a value that is there is read as it is
law value_kept:
  for +value: String
  for alt: String
  for full: {String.is_empty(value) == False{} : Bool}
  {Env.or_else(value, alt) == value : String}

# LAW: an empty value reads as the default
law empty_falls_back:
  for alt: String
  {Env.or_else("", alt) == alt : String}
