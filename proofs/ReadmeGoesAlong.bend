# proofs of laws/ReadmeGoesAlong.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/ReadmeGoesAlong.bend as Laws

def Laws.readme_goes_along(_tree, entry, seen, out, queue, text, here, fits):
  %here : {K.readme.put(_, K.readme(entry), entry, seen, out, queue)
    == K.made(entry, K.State{seen, K.Hit{"README.md", text} <> out, K.Going{}, queue})
    : K.Walked}
  %fits : {K.readme.sized(_, K.readme(entry), entry, text, seen, out, queue)
    == K.made(entry, K.State{seen, K.Hit{"README.md", text} <> out, K.Going{}, queue})
    : K.Walked}
  {==}
