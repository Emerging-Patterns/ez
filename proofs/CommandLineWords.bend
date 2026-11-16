# proofs of laws/CommandLineWords.bend
import Base
import ../src/share/args.bend as Args
import ../laws/CommandLineWords.bend as Laws

def Laws.words_after_program(_prog, _ws):
  {==}

def Laws.word_at_zero(_h, _t):
  {==}

def Laws.word_at_later(_h, _t, _n):
  {==}

# the empty list reads as no word at any place
def Laws.word_past_end(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.split_first(_h, _t):
  {==}

def Laws.env_set_reads(_value):
  {==}

def Laws.env_unset_empty(_e):
  {==}
