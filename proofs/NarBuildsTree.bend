# proofs of laws/NarBuildsTree.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/sha/nar.bend as Nar
import ../laws/NarBuildsTree.bend as Laws

# the type of the top decides, and each leaf is its own node
def Laws.nar_lone_file(_ex, _name, _at, _body):
  {==}

def Laws.nar_lone_symlink(_ex, _name, _at, _target):
  {==}

# the build of no paths closes the top at once
def Laws.nar_lone_directory(_ex, _name, _at, _body):
  {==}

# the file is inside the top because its path is its name under the top's
# empty path, and a string equals itself
def Laws.nar_file_in_directory(_dex, _dname, _dat, _dbody, ex, name, body):
  Equal.cong(Bool, Maybe<&2, String>,
    b => Nar.build.go(3n, Nar.step.ent(b, Nar.Ent{"f", ex, name, name, body}, [],
      Nar.Frame{"", "", []}, [])),
    String.eq(name, name), True{}, Eq.string_eq_self(name))

# a close with a directory around it is one step of the definition
def Laws.nar_close_nested(_at, _name, _kids, _pat, _pname, _pkids, _up, _es):
  {==}
