import Base
import ../src/pkg/pkg.bend as K

# What a package holds besides its sources and LICENSE files. bend 2.0.40
# takes along the file named exactly `README.md` in the entry's directory, at
# the top of the package, and hashes it with the rest; a README beside any
# other file stays out. It refuses a README over 65536 bytes, the most the hub
# takes, before it mines. That ez's walk and bend's publish agree is trusted
# in src/pkg/pkg.bend; these laws say what ez's side of it is. The walk's
# visit of a file takes along only the file, the LICENSE beside it and its
# foreign bodies (laws/LicenseGoesAlong.bend, laws/NoLicenseAsBefore.bend),
# so the README is the entry's alone.

# LAW: a walk that went to its end, whose entry has a README beside it the
# hub takes, publishes it at the top of the package
law readme_goes_along:
  for +tree: K.Tree
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  for text: String
  for here: {K.Here{text} == K.find(tree, K.readme(entry)) : K.Look}
  for fits: {False{} == K.readme.over(text) : Bool}
  {K.made.all(tree, entry, K.State{seen, out, K.Going{}, queue})
    == K.made(entry, K.State{seen, K.Hit{"README.md", text} <> out, K.Going{}, queue})
    : K.Walked}
