# What `src/pkg/print.bend` prints for a package: its hash on the first
# line, the directory its paths are written from on the second, then its
# manifest, so what `bend --publish` would upload can be read without
# uploading it. An unset EZ_ENTRY reads as no entry. A walk that stopped to
# ask for a file is taken up again with everything it had found and still
# had queued, going on. This is internal: the printer is a developer's tool,
# and the walk's resumption is the disk walk's (src/pkg/pkg.bend).
import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/print.bend as Print

# LAW: a package prints as its hash, its root and its manifest, a line each
law show_package:
  for h: String
  for root: String
  for fs: List<&2, K.Item>
  {Print.show(K.Pkg{h, root, fs}) == h ++ "\n" ++ root ++ "\n" ++ K.manifest_of(fs) : String}

# LAW: an environment variable that was set reads as its text
law text_of_set:
  for s: String
  {Print.text_of(Done{s}) == s : String}

# LAW: and one that was not reads as nothing
law text_of_unset:
  for e: U32 & String
  {Print.text_of(Fail{e}) == "" : String}

# LAW: a walk taken up again keeps what it saw, found and had queued, and
# goes on, whatever had stopped it
law resume_goes_on:
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for stop: K.Stop
  for queue: List<&2, K.Task>
  {K.resume(K.State{seen, out, stop, queue}) == K.State{seen, out, K.Going{}, queue} : K.State}
