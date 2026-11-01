# `ez publish` refuses, and sends nothing, when `git status --porcelain
# --untracked-files=normal` names any path, when git cannot answer it, or when
# a file of the package is one git does not track as unchanged (`git ls-files
# -v` tag `H`), an ignored file included.
#
# This guarantee and laws/PublishAgreesWithBend.bend are proved over the
# plan `ez publish` runs (`src/pub/plan.bend`). A World whose git status
# names a path, or that git cannot answer, is refused outright: nothing more
# is asked and nothing is sent (`pub_dirty_refuses`, `pub_gitless_refuses`,
# `pub_stop_sends_nothing`). A package holding a file git does not track as
# unchanged never reaches the upload (`pub_stray_sends_nothing`), and a
# World that does not reach it refuses (`pub_unsent_refuses`). A publish
# succeeds only when the upload's answer agrees with the hash ez computed
# (`pub_needs_agreement`), and the laws over `agrees` say what agreeing is:
# at least one line is a `0x` name and every such line is ez's hash. It then
# says ez's hash, never bend's (`pub_reports_ours`). bend 2.0.27 cannot
# report a package's hash without uploading it, so the upload is the last
# question the planner asks and the check is made on its answer;
# laws/PublishAgreesWithBend.bend promises that a disagreement exits 1 and
# prints no import line, not that nothing was sent. What the laws take from
# the interpreter is trusted in src/ez/app.bend: that it asks `git status`
# with `--untracked-files=normal` and `git ls-files -v` in the project, and
# runs the upload with the entry the planner names.
#
# They come in two layers. The decision functions of `ez publish`
# (pub/plan.bend) say what counts as bend's answer, whether that answer
# agrees with ez's hash, and whether the working tree and the package are
# clean enough to send. The plan laws say what the command does with them:
# stated over the plan the planner makes of a World and the questions it
# asks, so what they say of the plan is what the command does, the
# interpreter's faithfulness being trusted in src/ez/app.bend.
#
# `PP.stops(w)` is a World the command refuses outright, asking nothing more
# and sending nothing; `PP.sends(w)` a World at the upload or past it;
# `PP.succeeds(w)` one whose plan ends in success.
import Base
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/add/world.bend as A
import ../src/ez/start.bend as S

# ---------------------------------------------------------------------------
# the working tree and the package

# LAW: a tree is clean exactly when `git status --porcelain` named no path at
# all. The two walks are written independently, one looking for a line that
# says something and the other checking that every line says nothing, and this
# holds them to each other. What it pins down is the edge the whole refusal
# turns on: the empty line `String.lines` makes of a trailing newline is not a
# change, and every other line is, whatever its status code says.
law clean_is_all_blank:
  for ls: List<&2, String>
  {PP.blanks(ls) == Bool.not(PP.dirty.lines(ls)) : Bool}

# LAW: a status that names an untracked file is a dirty tree
law untracked_is_dirty:
  for path: String
  for rest: List<&2, String>
  {PP.dirty.lines(("?? " ++ path) <> rest) == True{} : Bool}

# LAW: and a modified file, ` M`
law modified_is_dirty:
  for path: String
  for rest: List<&2, String>
  {PP.dirty.lines((" M " ++ path) <> rest) == True{} : Bool}

# LAW: and a staged addition, `A `
law staged_is_dirty:
  for path: String
  for rest: List<&2, String>
  {PP.dirty.lines(("A  " ++ path) <> rest) == True{} : Bool}

# LAW: a file `git ls-files -v` marks `h`, assumed unchanged, is not tracked
# for publishing: `git status` does not report its changes, so its text on
# disk need not be the commit's
law assumed_is_untracked:
  for +path: String
  for rest: List<&2, String>
  {PP.tracked.has(("h " ++ path) <> rest, path) == PP.tracked.has(rest, path) : Bool}

# LAW: nor is one it marks `S`, skipped in the worktree, for the same reason
law skipped_is_untracked:
  for +path: String
  for rest: List<&2, String>
  {PP.tracked.has(("S " ++ path) <> rest, path) == PP.tracked.has(rest, path) : Bool}

# ---------------------------------------------------------------------------
# the plan

# LAW: `ez publish` on a World whose `git status --porcelain
# --untracked-files=normal` names a path refuses outright: it reads no file
# of the package, asks git nothing more, and sends nothing
law pub_dirty_refuses:
  for +w: PW.World
  for +text: String
  for e0: {PP.status(w) == PP.Said{text} : PP.Status}
  for e1: {PP.dirty(text) == True{} : Bool}
  {PP.stops(w) == True{} : Bool}

# LAW: and so does a World in which git could not answer that status: a
# directory in no repository has no commit for the package to exist in
law pub_gitless_refuses:
  for +w: PW.World
  for +why: String
  for e: {PP.status(w) == PP.StatusNo{why} : PP.Status}
  {PP.stops(w) == True{} : Bool}

# LAW: a package holding a file git does not track, an ignored one the entry
# imports among them, never gets as far as the upload
law pub_stray_sends_nothing:
  for +w: PW.World
  for +path: String
  for e: {PP.stray(w) == PP.Stray{path} : PP.Kept}
  {PP.sends(w) == False{} : Bool}

# LAW: a World the command refuses outright sends nothing
law pub_stop_sends_nothing:
  for +w: PW.World
  for r: {PP.stops(w) == True{} : Bool}
  {PP.sends(w) == False{} : Bool}

# LAW: and a World that never gets as far as the upload refuses: its plan
# does not succeed, so the command exits 1
law pub_unsent_refuses:
  for +w: PW.World
  for r: {PP.sends(w) == False{} : Bool}
  {PP.succeeds(w) == False{} : Bool}
