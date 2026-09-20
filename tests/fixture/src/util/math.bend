import Base

# the number, from the foreign side
def beep.ring(x: String) -> IO(String):
  import "./beep.c"
  import "./beep.js"

# double the number
def double(+x: U32) -> U32:
  (x * 2 : U32)
