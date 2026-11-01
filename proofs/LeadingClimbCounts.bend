# proofs of laws/LeadingClimbCounts.bend
import Base
import ../laws/LeadingClimbCounts.bend as Laws

# `../` splits into a climb and whatever the rest splits into, so the count
# computes down to one more than the rest's, with nothing left symbolic but
# the rest.
def Laws.ups_climb(_p):
  {==}
