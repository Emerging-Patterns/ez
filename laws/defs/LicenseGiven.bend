# whether the walk was given what it holds of the LICENSE beside a file
import Base
import ../../src/pkg/pkg.bend as K
import ../../src/lock/plan.bend as P
import ../../src/ez/named.bend as Named

# Named hub imports, `import <name>@<version>/<path> as P`, which bend 2.0.26
# added. The name is the first component of the normalised path when it
# holds an `@` (`K.named.of`), and the hub rules which names there are
# (`K.name.ok`, bend's `NAMED`).

# whether the walk was given what it holds of the LICENSE beside a file,
# there or not: a LICENSE it was not given is asked for first. Law
# vocabulary.
def given(look: K.Look) -> Bool:
  match look:
    case K.Here{_text}:
      True{}
    case K.Absent{}:
      True{}
    case K.Unasked{}:
      False{}
