# proofs of laws/LicenseAsked.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../laws/LicenseAsked.bend as Laws

def Laws.license_asked(tree, text, file, ns, eb, seen, out, rest, unasked):
  %unasked : {K.visit.put(K.asked(_, K.beside(file),
        _u => K.named.check(K.unnamed(K.scan.mods(K.scan(text))),
          _v => K.foreign.check(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(K.scan(text))))),
      tree, K.scan(text), text, file, ns, eb, seen, out, rest)
    == K.State{seen, out, K.Asking{K.beside(file)}, K.Task{file, ns} <> rest}
    : K.State}
  {==}
