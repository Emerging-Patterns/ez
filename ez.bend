# The program bend starts. Its directory is the project root, above every
# file, so Bend 2.0.28 gives each file one name. The program is ez/main.bend.
import Base
import ./ez/main.bend as Ez

def main() -> IO(Unit):
  Ez.main()
