# proofs of laws/OtherGitSourceLendsNoName.bend
import Base
import ../src/ez/named.bend as Named
import ../laws/OtherGitSourceLendsNoName.bend as Laws

def Laws.had_skips_git(n, _h, _en, _u, url, _rev, _tag, _root, _nar, _vend, t, fresh, ne):
  %ne : {Named.had.at(_, n, Named.had(t, url, fresh)) == Named.had(t, url, fresh)
    : String}
  {==}
