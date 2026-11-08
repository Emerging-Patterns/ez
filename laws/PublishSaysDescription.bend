# Once every check before the upload has passed, and just before the upload
# runs, `ez publish` prints `hub description: <line>` on stderr, the line the
# hub will describe the package by: the first line of the package's first file
# by path, in plain string order, passing over every file named `LICENSE` and
# the `README.md` bend 2.0.40 sends beside the entry. A publish refused before
# the upload prints only why.
#
# This guarantee is proved over the plan `ez publish` runs
# (`src/pub/plan.bend`) and `src/pub/blurb.bend`. The upload question
# carries the line (`pub_upload_says_description`), `B.blurb` of the files
# the walk made, which are the files bend sends: the entry, what it imports,
# since bend 2.0.27 the LICENSE beside each, and since 2.0.40 the README
# beside the entry (trusted in src/pkg/pkg.bend). A LICENSE never gives the
# line (`hub_license_named`, `hub_skips_license`), nor does the README
# (`hub_readme_named`, `hub_skips_readme`), and a file that is neither, whose
# path comes no later than any other file's, does, with its first line
# (`hub_first_by_path`), which is what comes before its first newline
# (`line_first_cut`). The hub's own listing shows it passes the README over:
# a package of LICENSE, README.md and main.bend is described by main.bend's
# first line. Paths are compared by `String.is_le`, the order the
# manifest is written in, which is JavaScript's for every path whose
# characters are in the Basic Multilingual Plane. The upload is the last
# question the planner asks, so a World the planner refuses before it never
# carries the line (`pub_stop_sends_nothing`, `pub_stray_sends_nothing`).
# That the hub picks the line this way is the hub's, not ez's: ez says what
# it expects the hub to show. What the laws take from the interpreter is
# trusted in src/ez/app.bend: that it prints the line the question carries
# just before it runs the upload, and at no other time.
import Base
import ../src/pkg/pkg.bend as K
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/pub/blurb.bend as B

# ---------------------------------------------------------------------------
# the hub description

# LAW: a text's first line is what comes before its first newline: a line
# with no newline in it, then a newline, then anything, has that line first
law line_first_cut:
  for a: String
  for +b: String
  for one: {B.has.nl(a) == False{} : Bool}
  {B.line.first(a ++ "\n" ++ b) == a : String}

# LAW: a file named LICENSE at the top of the package is one the hub passes
# over
law hub_license_named:
  for +t: String
  {B.lic(K.Source{"LICENSE", t}) == True{} : Bool}

# LAW: a LICENSE, wherever it stands in the package, never gives the
# description: the package describes itself as it would without it
law hub_skips_license:
  for +p: String
  for +t: String
  for fs: List<&2, K.Source>
  for l: {B.lic(K.Source{p, t}) == True{} : Bool}
  {B.blurb(K.Source{p, t} <> fs) == B.blurb(fs) : String}

# LAW: the README at the top of the package is one the hub passes over
law hub_readme_named:
  for +t: String
  {B.readme(K.Source{"README.md", t}) == True{} : Bool}

# LAW: the README never gives the description either: the package describes
# itself as it would without it
law hub_skips_readme:
  for +p: String
  for +t: String
  for fs: List<&2, K.Source>
  for r: {B.readme(K.Source{p, t}) == True{} : Bool}
  {B.blurb(K.Source{p, t} <> fs) == B.blurb(fs) : String}

# LAW: a file that is neither a LICENSE nor the README, whose path comes no
# later than any other file's, gives the description: its own first line,
# wherever the walk found it
law hub_first_by_path:
  for +p: String
  for +t: String
  for fs: List<&2, K.Source>
  for nl: {B.lic(K.Source{p, t}) == False{} : Bool}
  for nr: {B.readme(K.Source{p, t}) == False{} : Bool}
  for af: {B.after(p, fs) == True{} : Bool}
  {B.blurb(K.Source{p, t} <> fs) == B.line.first(t) : String}

# LAW: the upload is asked for with that line, the description of the
# package the walk made, and it is the only question that carries one, so a
# publish refused before the upload (`pub_stop_sends_nothing`,
# `pub_stray_sends_nothing`) says nothing but why
law pub_upload_says_description:
  for +w: PW.World
  {PP.upload(w) == PW.Upload{PP.entry(w), PP.named.word(PP.named(w)),
    "hub description: " ++ B.blurb(PP.files.of(PP.walked(w)))} : PW.Ask}
