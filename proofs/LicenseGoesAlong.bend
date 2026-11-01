# proofs of laws/LicenseGoesAlong.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../laws/LicenseGoesAlong.bend as Laws

def Laws.license_goes_along(tree, sc, text, file, ns, eb, seen, out, rest, lic, here):
  %here : {K.State{file <> seen,
      K.Hit{K.raw_of(ns, eb), text} <> List.append(&2, K.Hit,
        K.license.put(_, K.beside(K.raw_of(ns, eb))),
        List.append(&2, K.Hit,
          K.foreigns(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(sc)), out)),
      K.Going{},
      List.append(&2, K.Task, K.tasks(Path.dir(file), K.nsdir(ns), K.scan.mods(sc)), rest)}
    == K.State{file <> seen,
      K.Hit{K.raw_of(ns, eb), text} <> K.Hit{K.beside(K.raw_of(ns, eb)), lic}
        <> List.append(&2, K.Hit,
          K.foreigns(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(sc)), out),
      K.Going{},
      List.append(&2, K.Task, K.tasks(Path.dir(file), K.nsdir(ns), K.scan.mods(sc)), rest)}
    : K.State}
  {==}
