# proofs of laws/LiarHidesAnswerWhenMute.bend
import Base
import ../laws/LiarHidesAnswerWhenMute.bend as Laws

def Laws.bare_unless_mute(mute):
  match mute:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.mining_not_bare(_hash):
  {==}

def Laws.importing_not_bare(_hash):
  {==}

def Laws.unset_is_empty(_err):
  {==}

def Laws.set_is_text(_text):
  {==}
