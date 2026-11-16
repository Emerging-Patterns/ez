# The words of a `bend` ez runs under the memory cap, and what is said of
# one the cap killed. This is internal: it holds src/share/capped.bend in
# place, under `ez build`, `ez prove` and `ez tool`.
#
# An uncapped run is `env BEND_LIB=<lib>` followed by the program's words,
# unchanged. A capped run is the cap's scope (systemd-run with the memory
# limit) followed by exactly those same words, so the variable is set inside
# the cgroup and the program's own words are never touched. A run that ended
# with status 137 was killed for memory, and is said to have been, naming the
# cap; any run that was not killed has nothing said of it here. That 137 is
# what the kernel leaves on a process it killed for memory is trusted in
# src/share/cap.bend.
import Base
import ../src/share/capped.bend as Capped

# LAW: an uncapped run is BEND_LIB set in front of the program's words
law uncapped_words:
  for gigs: String
  for at: String
  for args: List<&2, String>
  {Capped.argv(False{}, gigs, at, args) == "env" <> (String.append("BEND_LIB=", at) <> args)
    : List<&2, String>}

# LAW: a capped run is the cap's scope in front of those same words
law capped_words:
  for gigs: String
  for at: String
  for args: List<&2, String>
  {Capped.argv(True{}, gigs, at, args)
    == List.append(&2, String, Capped.scope(gigs), "env" <> (String.append("BEND_LIB=", at) <> args))
    : List<&2, String>}

# LAW: a run that ended with status 137 was killed for memory
law status_137_killed:
  for text: String
  {Capped.killed(String.append("137\n", text)) == True{} : Bool}

# LAW: and is said to have been, naming the cap it ran under
law killed_names_cap:
  for text: String
  for gigs: String
  {Capped.why(String.append("137\n", text), gigs)
    == String.append("killed for memory at ", String.append(gigs, "G: raise EZ_CAP\n")) : String}

# LAW: a run that was not killed has nothing said of it
law unkilled_says_nothing:
  for out: String
  for gigs: String
  for alive: {Capped.killed(out) == False{} : Bool}
  {Capped.why(out, gigs) == "" : String}
