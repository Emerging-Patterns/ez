# proofs of laws/SourceOmitsAbsentTag.bend
import Base
import ../laws/SourceOmitsAbsentTag.bend as Laws

# The tag's line is the empty string, and nothing appended in front of a run
# of appends changes the run.
def Laws.source_omits_absent_tag(_url, _rev, _root, _nar):
  {==}
