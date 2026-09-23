# lock/up: what `ez lock --upgrade` decides, as a pure function of what the
# remote said. It is the upgrade half of the planner (lock/plan.bend): it reads
# the ledger and the answers to its own questions, and returns either the
# questions it still has, a refusal, or the ledger the lock is made from and
# everything the upgrade writes around it. The interpreter (lock/run.bend)
# answers each question by IO, and the planner turns the result into effects.
#
# A git dependency with a tag is re-resolved to that tag; one with only a
# commit fast-forwards to the default branch tip when the pin is an ancestor
# of it. A hub dependency is left, because the hash is the pin. `--package`
# selects one dependency or tool, and no other entry is asked about. A tool
# pin with no commit or no NAR hash is filled here and nowhere else. A moved
# dependency marked `vendor = true` has its new tree committed under
# `.ez/lib` and its old one removed, the gitignore allowlist is derived again
# from the ledger the upgrade leaves (`I.sync`), and an import that names a
# moved hash is rewritten. Nothing is written when the upgrade refuses: that
# is the planner's, since a refusal is a plan with no effects.
#
# A same commit is checked out and weighed, and `U.judge` is given whether
# that checkout agrees with the pin, so a pinned commit whose tree no longer
# hashes to the pin is `Drift` and refused.
import Base
import ./lock.bend as L
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/upgrade.bend as U
import ../manifest/ignore.bend as I
import ../git/git.bend as Git
import ../pkg/pkg.bend as K
import ../hub/hub.bend as Web
import ../sha/sha.bend as Sha
import ../ez/say.bend as Say

# ---------------------------------------------------------------------------
# questions and answers

# a question the upgrade asks, answered by one IO action. `ez add`
# (add/plan.bend) asks four of them too: `Tags`, `Head` and `Refs` to resolve
# a ref, and `Clone` for the checkout it walks, with `url` the source as git
# is to read it, which that planner anchors itself.
type Ask is Data:
  Refs{url: String, ref: String}                 # `git ls-remote url refs/tags/<ref> ... refs/heads/<ref>`
  Head{url: String}                              # `git ls-remote --symref url HEAD`
  Tags{url: String}                              # `git ls-remote --tags url`, for a tool with no tag
  Above{url: String, pin: String, tip: String}   # whether `tip` descends from `pin`
  Tree{url: String, rev: String, entry: String}  # a checkout at rev: narHash, root, the package its entry reaches
  Weigh{url: String, rev: String}                # a checkout at rev, narHash only, for a tool
  HubHas{hub: String, hash: String}              # the hub's manifest for a hash a dependency moved to
  Ignore{}                                       # `.gitignore`, "" when missing
  Sources{}                                      # every `.bend` file outside `.ez` and `.git`
  Clone{url: String, rev: String}                # a checkout at rev: narHash and every file's text, for `ez add`

# one source file of the project, with its text
type Found is Data:
  Found{at: String, text: String}

# the answer to one question. Git's output is kept as it was printed, with
# whether the command succeeded, so reading it is the planner's decision.
type Answer is Data:
  Printed{ok: Bool, text: String}                                              # Refs, Head, Tags
  Onward{yes: Bool}                                                            # Above
  Checkout{nar: String, root: String, manifest: String, srcs: List<&2, String>}  # Tree
  Weighed{nar: String}                                                         # Weigh
  HubSaid{got: Web.Got}                                                        # HubHas
  Text{text: String}                                                           # Ignore
  Files{files: List<&2, Found>}                                                # Sources
  Cloned{nar: String, files: List<&2, K.Source>}                               # Clone
  Miss{why: String}                                                            # any question IO could not answer

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# a tree checked out at a rev a dependency moved to: the package the lock
# reads for its new hash, so it is not cloned a second time
type Laid is Data:
  Laid{hash: String, nar: String, manifest: String, srcs: List<&2, String>}

# a file the upgrade writes: ez.toml, `.gitignore`, or a source
type Edit is Data:
  Edit{at: String, text: String}

# what the upgrade decided. `model` is the ledger model the upgrade renders
# into ez.toml, and ez.toml as it is when the upgrade refuses, still asks, or
# moves nothing; the upgrade's decisions are stated over it. `read` is the
# ledger the lock is made from: the one the upgrade writes, read back, or
# ez.toml as it is when nothing moved.
# `stop` is why the upgrade refuses, "" when it does not; a World with
# questions still open refuses too, and names them in `asks`. The rest is what
# the upgrade writes around the lock: the trees it checked out, the hashes
# committed under `.ez/lib`, the lines a person is told, ez.toml and
# `.gitignore` when they change, the project's sources, which it writes where
# a moved hash is rewritten (`edit.sources`), the committed trees it removes,
# and the hashes import lines stop naming, each with the hash that replaces
# it, which the lock reads the committed sources through. The sources are
# rewritten once, by the plan, and not on every round of questions.
type Next is Data:
  Next{model: M.Read, read: M.Read, stop: String, asks: List<&2, Ask>, trees: List<&2, Laid>,
    vends: List<&2, String>, says: List<&2, String>, edits: List<&2, Edit>,
    found: List<&2, Found>, drops: List<&2, String>, swaps: List<&2, U.Swap>}

def next.model(nx: Next) -> M.Read:
  Next{model, _read, _stop, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps} = nx
  model

def next.read(nx: Next) -> M.Read:
  Next{_model, read, _stop, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps} = nx
  read

def next.stop(nx: Next) -> String:
  Next{_model, _read, stop, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps} = nx
  stop

def next.asks(nx: Next) -> List<&2, Ask>:
  Next{_model, _read, _stop, asks, _trees, _vends, _says, _edits, _found, _drops, _swaps} = nx
  asks

def next.trees(nx: Next) -> List<&2, Laid>:
  Next{_model, _read, _stop, _asks, trees, _vends, _says, _edits, _found, _drops, _swaps} = nx
  trees

def next.vends(nx: Next) -> List<&2, String>:
  Next{_model, _read, _stop, _asks, _trees, vends, _says, _edits, _found, _drops, _swaps} = nx
  vends

def next.says(nx: Next) -> List<&2, String>:
  Next{_model, _read, _stop, _asks, _trees, _vends, says, _edits, _found, _drops, _swaps} = nx
  says

def next.edits(nx: Next) -> List<&2, Edit>:
  Next{_model, _read, _stop, _asks, _trees, _vends, _says, edits, _found, _drops, _swaps} = nx
  edits

def next.found(nx: Next) -> List<&2, Found>:
  Next{_model, _read, _stop, _asks, _trees, _vends, _says, _edits, found, _drops, _swaps} = nx
  found

def next.drops(nx: Next) -> List<&2, String>:
  Next{_model, _read, _stop, _asks, _trees, _vends, _says, _edits, _found, drops, _swaps} = nx
  drops

def next.swaps(nx: Next) -> List<&2, U.Swap>:
  Next{_model, _read, _stop, _asks, _trees, _vends, _says, _edits, _found, _drops, swaps} = nx
  swaps

# a plain lock: ez.toml as it is, and nothing around it
def plain(+read: M.Read) -> Next:
  Next{read, read, "", [], [], [], [], [], [], [], []}

# a refusal's reason, never empty. An empty reason is no refusal at all, so
# an upgrade that stopped with one would otherwise go on to lock the ledger
# as it was, and a pin that halted with one would drop out of the ledger the
# upgrade writes. The interpreter never answers with an empty reason.
def halt.why(+why: String) -> String:
  Bool.pick(String, String.is_empty(why), "ez: the upgrade stopped without a reason", why)

# an upgrade that refuses, or still asks: the lock is not made, and nothing is
# written
def stopped(+read: M.Read, +why: String, asks: List<&2, Ask>) -> Next:
  Next{read, read, halt.why(why), asks, [], [], [], [], [], [], []}

# ---------------------------------------------------------------------------
# looking an answer up

# a question as a key. A ledger value never holds a newline, so the fields
# are kept apart by one.
def key(ask: Ask) -> String:
  match ask:
    case Refs{url, ref}:
      "refs\n" ++ url ++ "\n" ++ ref
    case Head{url}:
      "head\n" ++ url
    case Tags{url}:
      "tags\n" ++ url
    case Above{url, pin, tip}:
      "above\n" ++ url ++ "\n" ++ pin ++ "\n" ++ tip
    case Tree{url, rev, entry}:
      "tree\n" ++ url ++ "\n" ++ rev ++ "\n" ++ entry
    case Weigh{url, rev}:
      "weigh\n" ++ url ++ "\n" ++ rev
    case HubHas{hub, hash}:
      "hub\n" ++ hub ++ "\n" ++ hash
    case Ignore{}:
      "ignore"
    case Sources{}:
      "sources"
    case Clone{url, rev}:
      "clone\n" ++ url ++ "\n" ++ rev

# an answer looked up, or none yet
type Heard is Data:
  Heard{answer: Answer}
  Open{}

# this answer when it is the question's, otherwise the rest's. The rest
# arrives as a thunk, so the first hit ends the scan.
def look.step(hit: Bool, answer: Answer, rest: Unit -> Heard) -> Heard:
  match hit:
    case True{}:
      Heard{answer}
    case False{}:
      rest(Unit{})

# the first answer given to a question
def look(rs: List<&2, Reply>, +want: String) -> Heard:
  match rs:
    case []:
      Open{}
    case Reply{ask, answer} <> t:
      look.step(String.eq(key(ask), want), answer, _u => look(t, want))

# the answer to a question, or none yet
def heard(rs: List<&2, Reply>, ask: Ask) -> Heard:
  look(rs, key(ask))

# what git printed, once it is known: the text, or why there is none, or the
# question still open
type Said is Data:
  Said{text: String}
  Unsaid{why: String}
  Unasked{ask: Ask}

def printed.ok(ok: Bool, +what: String, text: String) -> Said:
  match ok:
    case True{}:
      Said{text}
    case False{}:
      Unsaid{"ez: git " ++ what ++ ": " ++ String.trim(text)}

def printed.of(answer: Answer, +what: String) -> Said:
  match answer:
    case Printed{ok, text}:
      printed.ok(ok, what, text)
    case Miss{why}:
      Unsaid{why}
    case _:
      Unsaid{"ez: git " ++ what ++ " was not answered with what git printed"}

# what git printed for `what`
def printed.heard(got: Heard, ask: Ask, +what: String) -> Said:
  match got:
    case Open{}:
      Unasked{ask}
    case Heard{answer}:
      printed.of(answer, what)

# the same, looked up among the answers
def printed(rs: List<&2, Reply>, +ask: Ask, +what: String) -> Said:
  printed.heard(heard(rs, ask), ask, what)

# a file's text, "" when it is missing
def text.of(answer: Answer) -> Said:
  match answer:
    case Text{text}:
      Said{text}
    case Miss{why}:
      Unsaid{why}
    case _:
      Unsaid{"ez: a file was not answered with its text"}

def text.said.heard(got: Heard, ask: Ask) -> Said:
  match got:
    case Open{}:
      Unasked{ask}
    case Heard{answer}:
      text.of(answer)

# the same, looked up among the answers
def text.said(rs: List<&2, Reply>, +ask: Ask) -> Said:
  text.said.heard(heard(rs, ask), ask)

# a checkout, once it is known
type Co is Data:
  Co{nar: String, root: String, manifest: String, srcs: List<&2, String>}
  CoWait{ask: Ask}
  CoNo{why: String}

def checkout.of(answer: Answer) -> Co:
  match answer:
    case Checkout{nar, root, manifest, srcs}:
      Co{nar, root, manifest, srcs}
    case Miss{why}:
      CoNo{why}
    case _:
      CoNo{"ez: a checkout was not answered with one"}

# the checkout a question was answered with
def checkout.heard(got: Heard, ask: Ask) -> Co:
  match got:
    case Open{}:
      CoWait{ask}
    case Heard{answer}:
      checkout.of(answer)

# the same, looked up among the answers
def checkout(rs: List<&2, Reply>, +ask: Ask) -> Co:
  checkout.heard(heard(rs, ask), ask)

# ancestry, once it is known
type Asc is Data:
  Asc{yes: Bool}
  AscWait{ask: Ask}
  AscNo{why: String}

def onward.of(answer: Answer) -> Asc:
  match answer:
    case Onward{yes}:
      Asc{yes}
    case Miss{why}:
      AscNo{why}
    case _:
      AscNo{"ez: ancestry was not answered with whether it holds"}

# the ancestry a question was answered with
def onward.heard(got: Heard, ask: Ask) -> Asc:
  match got:
    case Open{}:
      AscWait{ask}
    case Heard{answer}:
      onward.of(answer)

# the same, looked up among the answers
def onward(rs: List<&2, Reply>, +ask: Ask) -> Asc:
  onward.heard(heard(rs, ask), ask)

# a NAR hash, once it is known
type Wd is Data:
  Wd{nar: String}
  WdWait{ask: Ask}
  WdNo{why: String}

def weighed.of(answer: Answer) -> Wd:
  match answer:
    case Weighed{nar}:
      Wd{nar}
    case Miss{why}:
      WdNo{why}
    case _:
      WdNo{"ez: a weighing was not answered with a NAR hash"}

# the NAR hash a question was answered with
def weighed.heard(got: Heard, ask: Ask) -> Wd:
  match got:
    case Open{}:
      WdWait{ask}
    case Heard{answer}:
      weighed.of(answer)

# the same, looked up among the answers
def weighed(rs: List<&2, Reply>, +ask: Ask) -> Wd:
  weighed.heard(heard(rs, ask), ask)

# the hub's word on a hash, once it is known. It stops the upgrade only when a
# manifest arrived under the hash and did not hash to it.
type Hubbed is Data:
  Clear{}
  Clash{}
  HubWait{ask: Ask}
  HubNo{why: String}

def hub.got(got: Web.Got) -> Hubbed:
  match got:
    case Web.Have{_body}:
      Clear{}
    case Web.Miss{why}:
      Bool.pick(Hubbed, U.hub.bad(why), Clash{}, Clear{})

def hub.of(answer: Answer) -> Hubbed:
  match answer:
    case HubSaid{got}:
      hub.got(got)
    case Miss{why}:
      HubNo{why}
    case _:
      HubNo{"ez: the hub was not answered with what it served"}

# the hub's word a question was answered with
def hubbed.heard(got: Heard, ask: Ask) -> Hubbed:
  match got:
    case Open{}:
      HubWait{ask}
    case Heard{answer}:
      hub.of(answer)

# the same, looked up among the answers
def hubbed(rs: List<&2, Reply>, +ask: Ask) -> Hubbed:
  hubbed.heard(heard(rs, ask), ask)

# the project's sources, once they are known
type Srcs is Data:
  Srcs{files: List<&2, Found>}
  SrcsWait{ask: Ask}
  SrcsNo{why: String}

def sources.of(answer: Answer) -> Srcs:
  match answer:
    case Files{fs}:
      Srcs{fs}
    case Miss{why}:
      SrcsNo{why}
    case _:
      SrcsNo{"ez: the sources were not answered with their texts"}

# the sources a question was answered with
def sources.heard(got: Heard, ask: Ask) -> Srcs:
  match got:
    case Open{}:
      SrcsWait{ask}
    case Heard{answer}:
      sources.of(answer)

# the same, looked up among the answers
def sources(rs: List<&2, Reply>, +ask: Ask) -> Srcs:
  sources.heard(heard(rs, ask), ask)

# ---------------------------------------------------------------------------
# what a ref names

# the commit a pin is asked to move to, the tag it came through ("" for
# none), and the default branch it tips ("" for a tag); or the question still
# open, or why there is no answer
type Tip is Data:
  At{rev: String, tag: String, branch: String}
  TipWait{ask: Ask}
  TipNo{why: String}

# the commit the rows name for a ref. A ref the remote does not have is a
# mistake worth naming.
def follow.rev(+rev: String, +url: String, +ref: String) -> Tip:
  Bool.pick(Tip, String.is_empty(rev), TipNo{"ez: " ++ url ++ " has no ref named " ++ ref},
    At{rev, ref, ""})

def follow.said(said: Said, +url: String, +ref: String) -> Tip:
  match said:
    case Said{text}:
      follow.rev(Git.exact(Git.rows(String.lines(text)), ref), url, ref)
    case Unsaid{why}:
      TipNo{why}
    case Unasked{ask}:
      TipWait{ask}

def follow.ask(pinned: Bool, +rs: List<&2, Reply>, +url: String, +ref: String) -> Tip:
  match pinned:
    case True{}:
      At{ref, "", ""}
    case False{}:
      follow.said(printed(rs, Refs{url, ref}, "ls-remote " ++ url), url, ref)

# the commit a ref names, as `Git.resolve` reads it: a 40-hex ref is a commit
# already, and asks the remote nothing
def follow(+rs: List<&2, Reply>, +url: String, +ref: String) -> Tip:
  follow.ask(Git.is_rev(ref), rs, url, ref)

# a remote with no HEAD is not one an upgrade can move
def forward.rev(+rev: String, branch: String, +url: String) -> Tip:
  Bool.pick(Tip, String.is_empty(rev), TipNo{"ez: " ++ url ++ " has no HEAD"},
    At{rev, "", branch})

def forward.said(said: Said, +url: String) -> Tip:
  match said:
    case Said{text}:
      +rows = Git.rows(String.lines(text))
      forward.rev(Git.tip.rev(rows), Git.tip.branch(rows), url)
    case Unsaid{why}:
      TipNo{why}
    case Unasked{ask}:
      TipWait{ask}

# the commit the default branch tips, and its name
def forward(+rs: List<&2, Reply>, +url: String) -> Tip:
  forward.said(printed(rs, Head{url}, "ls-remote " ++ url), url)

# the word Off quotes: a branch name when there is one, otherwise the commit
def tip.of(+branch: String, +tip: String) -> String:
  Bool.pick(String, String.is_empty(branch), tip, branch)

# a tag that moved off the pin's history, or a branch tip that does not
# descend from a rev-only pin
def off.why(+name: String, +tag: String, +pin: String, +tip: String) -> String:
  Bool.pick(String, String.is_empty(tag),
    "ez: " ++ name ++ ": " ++ pin ++ " is not an ancestor of " ++ tip,
    "ez: " ++ name ++ ": tag " ++ tag ++ " moved off " ++ pin)

# the branch a rev-only pin followed, said when there is one
def branch.of(+label: String) -> String:
  Bool.pick(String, String.is_empty(label), "", " (" ++ label ++ ")")

# a line saying a pin moved
def say.move(+name: String, +old: String, +new: String, +branch: String) -> String:
  name ++ ": " ++ old ++ " -> " ++ new ++ branch.of(branch)

# the `0x` name a manifest is the digest of
def hash.of(+manifest: String) -> String:
  "0x" ++ String.take(Sha.hex(manifest), 32n)

# ---------------------------------------------------------------------------
# one dependency

# what one dependency became: its entry in the ledger the upgrade leaves, the
# committed tree to remove ("" for none), its new hash, the hash an import
# must stop naming ("" for none), whether it moved, what a person is told, and
# the tree checked out at its new rev. Or the questions still open, or why the
# upgrade refuses.
type Fate is Data:
  Became{dep: M.Dep, old: String, new: String, prev: String, moved: Bool,
    says: List<&2, String>, trees: List<&2, Laid>}
  Waits{asks: List<&2, Ask>}
  Halts{why: String}

# a dependency left as it was
def stay(dep: M.Dep, says: List<&2, String>) -> Fate:
  Became{dep, "", "", "", False{}, says, []}

# the old hash, or "" when it did not change
def swap.hash(same: Bool, +old: String) -> String:
  match same:
    case True{}:
      ""
    case False{}:
      old

# a committed tree whose hash changed is a tree to remove
def swap.of(vend: Bool, +old: String, +new: String) -> String:
  match vend:
    case False{}:
      ""
    case True{}:
      swap.hash(String.eq(old, new), old)

# a line, only when there is something to say
def line.if(say: Bool, +text: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, say, [text], [])

# a moved pin, once the hub has not objected to its new hash: the ledger's
# entry retargeted, the committed tree it replaces, the hash imports stop
# naming, and what a person is told
def dep.moved(
  +dep: M.Dep,
  +hash: String,
  +rev: String,
  +root: String,
  +nar: String,
  manifest: String,
  srcs: List<&2, String>,
  +branch: String
) -> Fate:
  +src = M.source.dep(dep)
  +name = M.dep.name(dep)
  +old = M.dep.hash(dep)
  +drop = swap.of(M.source.vendor(src), old, hash)
  +prev = swap.hash(String.eq(old, hash), old)
  Became{U.retarget(dep, rev, hash, root, nar), drop, hash, prev, True{},
    say.move(name, M.source.rev(src), rev, branch) <>
      List.append(&2, String,
        line.if(Bool.not(String.is_empty(prev)), name ++ ": imports " ++ old ++ " -> " ++ hash),
        line.if(Bool.not(String.is_empty(drop)), name ++ ": vendored .ez/lib/" ++ hash)),
    [Laid{hash, nar, manifest, srcs}]}

# the hub's word on the new hash
def dep.hub(
  hubbed: Hubbed,
  +dep: M.Dep,
  +hash: String,
  +rev: String,
  +root: String,
  +nar: String,
  manifest: String,
  srcs: List<&2, String>,
  +branch: String
) -> Fate:
  match hubbed:
    case Clear{}:
      dep.moved(dep, hash, rev, root, nar, manifest, srcs, branch)
    case Clash{}:
      Halts{"ez: " ++ M.dep.name(dep) ++ ": hub digest does not match " ++ hash}
    case HubWait{ask}:
      Waits{[ask]}
    case HubNo{why}:
      Halts{why}

# the checkout at the rev the pin advances to, then the hub asked about the
# hash it has. The hub a moved hash is checked against is the ledger's.
def dep.advance(co: Co, +rs: List<&2, Reply>, +hub: String, +dep: M.Dep, +rev: String, +branch: String) -> Fate:
  match co:
    case Co{nar, root, +manifest, srcs}:
      +hash = hash.of(manifest)
      dep.hub(hubbed(rs, HubHas{hub, hash}), dep, hash, rev, root, nar, manifest, srcs,
        branch)
    case CoWait{ask}:
      Waits{[ask]}
    case CoNo{why}:
      Halts{why}

# the verdict. `seen` is the hash the pinned commit's checkout has, which a
# drift names; "" when the commit moved and the pin was not checked out.
def dep.verdict(
  verdict: U.Verdict,
  +rs: List<&2, Reply>,
  +hub: String,
  +dep: M.Dep,
  +tip: String,
  +branch: String,
  +seen: String
) -> Fate:
  match verdict:
    case U.Keep{}:
      stay(dep, [M.dep.name(dep) ++ ": unchanged " ++ M.source.rev(M.source.dep(dep))])
    case U.Drift{}:
      +src = M.source.dep(dep)
      Halts{Say.drift(M.dep.name(dep), M.source.tag(src), M.source.rev(src),
        M.dep.hash(dep), seen)}
    case U.Off{}:
      +src = M.source.dep(dep)
      Halts{off.why(M.dep.name(dep), M.source.tag(src), M.source.rev(src),
        tip.of(branch, tip))}
    case U.Advance{+rev, _tag}:
      dep.advance(checkout(rs, Tree{M.source.url(M.source.dep(dep)), rev, M.dep.entry(dep)}), rs, hub, dep, rev, branch)

# the pinned commit's checkout, judged with whether it agrees with the pin:
# the same hash, NAR hash and root. One that does not is a drift.
def dep.kept(co: Co, +rs: List<&2, Reply>, +hub: String, +dep: M.Dep, +tip: String, +tag: String) -> Fate:
  match co:
    case Co{nar, root, manifest, _srcs}:
      +src = M.source.dep(dep)
      +hash = hash.of(manifest)
      dep.verdict(U.judge(True{}, True{},
        U.agree(M.dep.hash(dep), hash, M.source.nar(src), nar, M.source.root(src), root),
        tip, tag), rs, hub, dep, tip, "", hash)
    case CoWait{ask}:
      Waits{[ask]}
    case CoNo{why}:
      Halts{why}

# a different commit, once ancestry is known. The commit moved, so no
# checkout at the pin was weighed and none agrees with it.
def dep.onward(
  asc: Asc,
  +rs: List<&2, Reply>,
  +hub: String,
  +dep: M.Dep,
  +tip: String,
  +tag: String,
  +branch: String
) -> Fate:
  match asc:
    case Asc{yes}:
      dep.verdict(U.judge(False{}, yes, False{}, tip, tag), rs, hub, dep, tip,
        branch, "")
    case AscWait{ask}:
      Waits{[ask]}
    case AscNo{why}:
      Halts{why}

# the same commit is checked out to be weighed; a different one is asked
# whether it descends from the pin
def dep.same(
  same: Bool,
  +rs: List<&2, Reply>,
  +hub: String,
  +dep: M.Dep,
  +tip: String,
  +tag: String,
  +branch: String
) -> Fate:
  match same:
    case True{}:
      +src = M.source.dep(dep)
      dep.kept(checkout(rs, Tree{M.source.url(src), M.source.rev(src), M.dep.entry(dep)}), rs, hub, dep, tip, tag)
    case False{}:
      +src = M.source.dep(dep)
      dep.onward(onward(rs, Above{M.source.url(src), M.source.rev(src), tip}), rs, hub, dep, tip, tag, branch)

# the commit the remote names, against the pin
def dep.tip(tip: Tip, +rs: List<&2, Reply>, +hub: String, +dep: M.Dep) -> Fate:
  match tip:
    case At{+rev, tag, branch}:
      dep.same(String.eq(M.source.rev(M.source.dep(dep)), rev), rs, hub, dep, rev,
        tag, branch)
    case TipWait{ask}:
      Waits{[ask]}
    case TipNo{why}:
      Halts{why}

# a hub pin named with `--package` is reported and left. An unselected
# dependency is left quietly.
def dep.hold(sel: Bool, +dep: M.Dep) -> Fate:
  stay(dep, line.if(sel, M.dep.name(dep) ++ ": pinned by its hash"))

# one dependency, by what it is asked
def dep.one(aim: U.Aim, +rs: List<&2, Reply>, +only: String, +hub: String, +dep: M.Dep) -> Fate:
  match aim:
    case U.Hold{}:
      dep.hold(U.chosen(only, M.dep.name(dep)), dep)
    case U.Follow{ref}:
      dep.tip(follow(rs, M.source.url(M.source.dep(dep)), ref), rs, hub, dep)
    case U.Forward{}:
      dep.tip(forward(rs, M.source.url(M.source.dep(dep))), rs, hub, dep)

# every dependency after the upgrade: the ledger's entries in its order, the
# committed trees that moved (`swaps`), the hashes import lines stop naming
# (`edits`), whether any pin moved, what a person is told, the trees checked
# out, the questions still open, and the first refusal, "" for none
type Deps is Data:
  Deps{deps: List<&2, M.Dep>, swaps: List<&2, U.Swap>, edits: List<&2, U.Swap>,
    moved: Bool, says: List<&2, String>, trees: List<&2, Laid>,
    asks: List<&2, Ask>, bad: String}

# a moved hash, kept only when there is one
def swaps.put(empty: Bool, +old: String, +new: String, rest: List<&2, U.Swap>) -> List<&2, U.Swap>:
  match empty:
    case True{}:
      rest
    case False{}:
      U.Swap{old, new} <> rest

# one dependency in front of the rest. A refusal ahead of the rest wins, so
# the first in ledger order is the one given.
def deps.join(fate: Fate, rest: Deps) -> Deps:
  match fate:
    case Became{d, +old, +new, +prev, m, says, trees}:
      Deps{ds, ss, es, any, sy, tr, asks, bad} = rest
      Deps{d <> ds, swaps.put(String.is_empty(old), old, new, ss),
        swaps.put(String.is_empty(prev), prev, new, es), Bool.or(m, any),
        List.append(&2, String, says, sy), List.append(&2, Laid, trees, tr), asks, bad}
    case Waits{more}:
      Deps{ds, ss, es, any, sy, tr, asks, bad} = rest
      Deps{ds, ss, es, any, sy, tr, List.append(&2, Ask, more, asks), bad}
    case Halts{why}:
      Deps{ds, ss, es, any, sy, tr, asks, _bad} = rest
      Deps{ds, ss, es, any, sy, tr, asks, halt.why(why)}

# every dependency, in the order the ledger wrote them
def deps.walk(+rs: List<&2, Reply>, +only: String, +hub: String, ds: List<&2, M.Dep>) -> Deps:
  match ds:
    case []:
      Deps{[], [], [], False{}, [], [], [], ""}
    case +h <> t:
      deps.join(dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs,
        only, hub, h), deps.walk(rs, only, hub, t))

# ---------------------------------------------------------------------------
# one tool

# one tool after it was asked about, or the questions still open, or why the
# upgrade refuses
type Pinned is Data:
  Pinned{tool: M.Tool, moved: Bool, says: List<&2, String>}
  PinWait{asks: List<&2, Ask>}
  PinHalt{why: String}

# the pin with a commit and a NAR hash written in. An empty tag leaves the one
# the ledger already had. The vendor bit is off: a tool is not committed under
# `.ez/lib`.
def set.go(
  +name: String,
  +entry: String,
  +bin: String,
  source: M.Source,
  +rev: String,
  +tag: String,
  +nar: String
) -> M.Tool:
  match source:
    case M.Hub{}:
      M.Tool{name, entry, bin, M.Hub{}}
    case M.Git{url, _rev, old, root, _nar, _vend}:
      M.Tool{name, entry, bin, M.Git{url, rev,
        Bool.pick(String, String.is_empty(tag), old, tag), M.root.or(root),
        nar, False{}}}

# a tool's pin with a commit, a tag and a NAR hash written in
def set(tool: M.Tool, +rev: String, +tag: String, +nar: String) -> M.Tool:
  M.Tool{n, e, b, s} = tool
  set.go(n, e, b, s, rev, tag, nar)

# a commit and its NAR hash written into the pin. A pin with either one empty
# is short, and an upgrade that wrote one would fill it again on the next run,
# so a weighing that names no commit or no NAR hash pins nothing.
def tool.pin(short: Bool, +tool: M.Tool, +rev: String, +tag: String, +nar: String, says: List<&2, String>) -> Pinned:
  match short:
    case True{}:
      PinHalt{"ez: tools." ++ M.tool.name(tool) ++ ": weighing " ++ rev ++ " gave no narHash"}
    case False{}:
      Pinned{set(tool, rev, tag, nar), True{}, says}

# a commit weighed, then written into the pin
def tool.weighed(wd: Wd, +tool: M.Tool, +rev: String, +tag: String, says: List<&2, String>) -> Pinned:
  match wd:
    case Wd{+nar}:
      tool.pin(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case WdWait{ask}:
      PinWait{[ask]}
    case WdNo{why}:
      PinHalt{why}

# the commit a ref named, weighed. The pin records the ref as its tag, even
# one that names a commit, so the next upgrade asks about the same ref.
def tool.resolved(tip: Tip, +rs: List<&2, Reply>, +tool: M.Tool, +ref: String) -> Pinned:
  match tip:
    case At{+rev, _tag, _branch}:
      tool.weighed(weighed(rs, Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
    case TipWait{ask}:
      PinWait{[ask]}
    case TipNo{why}:
      PinHalt{why}

# the ref a pin with no commit is pinned from, once it is known
type Named is Data:
  Named{ref: String}
  NamedWait{ask: Ask}
  NamedNo{why: String}

# a remote whose HEAD names no branch leaves nothing to pin
def heads.branch(+name: String, +url: String) -> Named:
  Bool.pick(Named, String.is_empty(name),
    NamedNo{"ez: " ++ url ++
      " has no semver-ish tag and its HEAD names no branch; name a ref to pin"},
    Named{name})

def heads.said(said: Said, +url: String) -> Named:
  match said:
    case Said{text}:
      heads.branch(Git.tip.branch(Git.rows(String.lines(text))), url)
    case Unsaid{why}:
      NamedNo{why}
    case Unasked{ask}:
      NamedWait{ask}

# the greatest semver-ish tag, else the default branch
def tags.best(none: Bool, +best: String, +rs: List<&2, Reply>, +url: String) -> Named:
  match none:
    case False{}:
      Named{best}
    case True{}:
      heads.said(printed(rs, Head{url}, "ls-remote " ++ url), url)

def tags.said(said: Said, +rs: List<&2, Reply>, +url: String) -> Named:
  match said:
    case Said{text}:
      +best = Git.choose(Git.tag.names(Git.rows(String.lines(text))))
      tags.best(String.is_empty(best), best, rs, url)
    case Unsaid{why}:
      NamedNo{why}
    case Unasked{ask}:
      NamedWait{ask}

# the ref `ez add` pins when none was asked for: the greatest semver-ish
# release tag, else the greatest pre-release, else the default branch
def tool.default(+rs: List<&2, Reply>, +url: String) -> Named:
  tags.said(printed(rs, Tags{url}, "ls-remote " ++ url), rs, url)

# the ref to resolve: the tag the ledger named, or the default ref
def tool.ref(no_tag: Bool, +rs: List<&2, Reply>, +url: String, +tag: String) -> Named:
  match no_tag:
    case False{}:
      Named{tag}
    case True{}:
      tool.default(rs, url)

def tool.named(named: Named, +rs: List<&2, Reply>, +tool: M.Tool, +url: String) -> Pinned:
  match named:
    case Named{+ref}:
      tool.resolved(follow(rs, url, ref), rs, tool, ref)
    case NamedWait{ask}:
      PinWait{[ask]}
    case NamedNo{why}:
      PinHalt{why}

# the verdict on a full pin. A pin that moves keeps its own tag, as a
# dependency does: the tip was named by that tag, or by the default branch
# for a pin with none.
def tool.verdict(verdict: U.Verdict, +rs: List<&2, Reply>, +tool: M.Tool, +tip: String, +branch: String) -> Pinned:
  match verdict:
    case U.Keep{}:
      Pinned{tool, False{}, [M.tool.name(tool) ++ ": unchanged " ++
        M.source.rev(M.tool.source(tool))]}
    case U.Drift{}:
      PinHalt{"ez: " ++ M.tool.name(tool) ++ ": narHash drifted at " ++
        M.source.rev(M.tool.source(tool))}
    case U.Off{}:
      +src = M.tool.source(tool)
      PinHalt{off.why(M.tool.name(tool), M.source.tag(src), M.source.rev(src),
        tip.of(branch, tip))}
    case U.Advance{+rev, _tag}:
      +src = M.tool.source(tool)
      tool.weighed(weighed(rs, Weigh{M.source.url(src), rev}), tool, rev, "",
        [say.move(M.tool.name(tool), M.source.rev(src), rev, branch)])

# the pinned commit weighed: its NAR hash written in when the pin has none,
# else judged with whether it is the one the pin records
def tool.kept.nar(fill: Bool, +rs: List<&2, Reply>, +tool: M.Tool, +tip: String, +tag: String, +nar: String) -> Pinned:
  match fill:
    case True{}:
      tool.pin(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tool.verdict(U.judge(True{}, True{},
        String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag), rs, tool, tip, "")

# the pinned commit weighed again
def tool.kept(wd: Wd, +rs: List<&2, Reply>, +tool: M.Tool, +tip: String, +tag: String) -> Pinned:
  match wd:
    case Wd{+nar}:
      tool.kept.nar(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
    case WdWait{ask}:
      PinWait{[ask]}
    case WdNo{why}:
      PinHalt{why}

def tool.onward(asc: Asc, +rs: List<&2, Reply>, +tool: M.Tool, +tip: String, +tag: String, +branch: String) -> Pinned:
  match asc:
    case Asc{yes}:
      tool.verdict(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case AscWait{ask}:
      PinWait{[ask]}
    case AscNo{why}:
      PinHalt{why}

def tool.same(same: Bool, +rs: List<&2, Reply>, +tool: M.Tool, +tip: String, +tag: String, +branch: String) -> Pinned:
  match same:
    case True{}:
      +src = M.tool.source(tool)
      tool.kept(weighed(rs, Weigh{M.source.url(src), M.source.rev(src)}), rs, tool, tip, tag)
    case False{}:
      +src = M.tool.source(tool)
      tool.onward(onward(rs, Above{M.source.url(src), M.source.rev(src), tip}), rs, tool, tip, tag, branch)

def tool.tip(tip: Tip, +rs: List<&2, Reply>, +tool: M.Tool) -> Pinned:
  match tip:
    case At{+rev, tag, branch}:
      tool.same(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev,
        tag, branch)
    case TipWait{ask}:
      PinWait{[ask]}
    case TipNo{why}:
      PinHalt{why}

# a full pin, re-asked: its tag re-resolved, or the default branch followed
def tool.aim(aim: U.Aim, +rs: List<&2, Reply>, +tool: M.Tool) -> Pinned:
  match aim:
    case U.Hold{}:
      Pinned{tool, False{}, []}
    case U.Follow{ref}:
      tool.tip(follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      tool.tip(forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

# a pin with no commit is resolved from its tag, or the default ref, then
# weighed. One with a commit and no NAR hash is upgraded as a full pin is,
# and its NAR hash is written in wherever it lands: filled at its own commit
# only, it would move on the next upgrade, which follows its tag or the
# default branch.
def tool.fill(no_rev: Bool, +rs: List<&2, Reply>, +tool: M.Tool) -> Pinned:
  match no_rev:
    case True{}:
      +src = M.tool.source(tool)
      +url = M.source.url(src)
      tool.named(tool.ref(String.is_empty(M.source.tag(src)), rs, url,
        M.source.tag(src)), rs, tool, url)
    case False{}:
      tool.aim(U.aim(True{}, M.tool.source(tool)), rs, tool)

# a selected pin with no commit or no NAR hash is filled; a full one is asked
# whether it moved
def tool.short(short: Bool, +rs: List<&2, Reply>, +tool: M.Tool) -> Pinned:
  match short:
    case True{}:
      tool.fill(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      tool.aim(U.aim(True{}, M.tool.source(tool)), rs, tool)

# a selected tool names a repo, or it cannot be pinned
def tool.git(git: Bool, +rs: List<&2, Reply>, +tool: M.Tool) -> Pinned:
  match git:
    case False{}:
      PinHalt{"ez: tools." ++ M.tool.name(tool) ++ " has no git"}
    case True{}:
      +src = M.tool.source(tool)
      tool.short(Bool.or(String.is_empty(M.source.rev(src)),
        String.is_empty(M.source.nar(src))), rs, tool)

# a selected tool is asked; the others are left
def tool.sel(sel: Bool, +rs: List<&2, Reply>, +tool: M.Tool) -> Pinned:
  match sel:
    case False{}:
      Pinned{tool, False{}, []}
    case True{}:
      tool.git(M.source.is_git(M.tool.source(tool)), rs, tool)

# every tool after the upgrade, as `Deps` is for dependencies
type Tools is Data:
  Tools{tools: List<&2, M.Tool>, moved: Bool, says: List<&2, String>,
    asks: List<&2, Ask>, bad: String}

def tools.join(pinned: Pinned, rest: Tools) -> Tools:
  match pinned:
    case Pinned{t, m, says}:
      Tools{ts, any, sy, asks, bad} = rest
      Tools{t <> ts, Bool.or(m, any), List.append(&2, String, says, sy), asks, bad}
    case PinWait{more}:
      Tools{ts, any, sy, asks, bad} = rest
      Tools{ts, any, sy, List.append(&2, Ask, more, asks), bad}
    case PinHalt{why}:
      Tools{ts, any, sy, asks, _bad} = rest
      Tools{ts, any, sy, asks, halt.why(why)}

# every tool, in the order the ledger wrote them
def tools.walk(+rs: List<&2, Reply>, +only: String, ts: List<&2, M.Tool>) -> Tools:
  match ts:
    case []:
      Tools{[], False{}, [], [], ""}
    case +h <> t:
      tools.join(tool.sel(U.chosen(only, M.tool.name(h)), rs, h),
        tools.walk(rs, only, t))

# ---------------------------------------------------------------------------
# what the upgrade writes around the lock

# ez.toml, only when a pin moved, so an upgrade that changed nothing does not
# reformat the file
def edit.toml(moved: Bool, +text: String, rest: List<&2, Edit>) -> List<&2, Edit>:
  match moved:
    case True{}:
      Edit{"ez.toml", text} <> rest
    case False{}:
      rest

# a file, only when its text changes
def edit.if(same: Bool, +at: String, +text: String, rest: List<&2, Edit>) -> List<&2, Edit>:
  match same:
    case True{}:
      rest
    case False{}:
      Edit{at, text} <> rest

# every source with each moved hash rewritten in its imports, written only
# when that changes it
def edit.sources(fs: List<&2, Found>, +es: List<&2, U.Swap>) -> List<&2, Edit>:
  match fs:
    case []:
      []
    case Found{+at, +text} <> t:
      +next = U.reimport.many(es, text)
      edit.if(String.eq(next, text), at, next, edit.sources(t, es))

# every committed tree that moved, removed
def drops.of(ss: List<&2, U.Swap>) -> List<&2, String>:
  match ss:
    case []:
      []
    case U.Swap{old, _new} <> t:
      old <> drops.of(t)

# the ledger the lock is made from: the one the upgrade writes, read back, or
# ez.toml as it was when nothing moved
def read.next(moved: Bool, +text: String, old: M.Manifest) -> M.Read:
  match moved:
    case True{}:
      M.parse(text)
    case False{}:
      M.Good{old}

# the ledger model the upgrade renders, or ez.toml's when nothing moved
def model.next(moved: Bool, next: M.Manifest, old: M.Manifest) -> M.Read:
  match moved:
    case True{}:
      M.Good{next}
    case False{}:
      M.Good{old}

# every answer in: the ledger, the allowlist and the imports, and the trees
def done(
  +old: M.Manifest,
  dd: Deps,
  tt: Tools,
  +ignore: String,
  fs: List<&2, Found>
) -> Next:
  M.Manifest{+name, +entry, +bin, +hub, _ds, _ts} = old
  Deps{+ds, swaps, +edits, dmoved, dsays, trees, _dasks, _dbad} = dd
  Tools{+ts, tmoved, tsays, _tasks, _tbad} = tt
  +moved = Bool.or(dmoved, tmoved)
  +text = Rend.show(M.Manifest{name, entry, bin, hub, ds, ts})
  +allow = I.sync(ds, ignore)
  Next{model.next(moved, M.Manifest{name, entry, bin, hub, ds, ts}, old),
    read.next(moved, text, old), "", [], trees, I.vended(ds),
    List.append(&2, String, dsays, tsays),
    edit.toml(moved, text, edit.if(String.eq(allow, ignore), ".gitignore", allow, [])),
    fs, drops.of(swaps), edits}

# the question still open, when one is
def open.srcs(srcs: Srcs) -> List<&2, Ask>:
  match srcs:
    case SrcsWait{ask}:
      [ask]
    case _:
      []

# the sources, once the ignore file is known
def got.srcs(srcs: Srcs, +old: M.Manifest, dd: Deps, tt: Tools, +ignore: String) -> Next:
  match srcs:
    case Srcs{fs}:
      done(old, dd, tt, ignore, fs)
    case SrcsWait{ask}:
      stopped(M.Good{old}, "ez: the upgrade was not given the project's sources", [ask])
    case SrcsNo{why}:
      stopped(M.Good{old}, why, [])

# the ignore file, then the sources
def got.ignore(said: Said, +srcs: Srcs, +old: M.Manifest, dd: Deps, tt: Tools) -> Next:
  match said:
    case Said{ignore}:
      got.srcs(srcs, old, dd, tt, ignore)
    case Unasked{ask}:
      stopped(M.Good{old}, "ez: the upgrade was not given .gitignore",
        ask <> open.srcs(srcs))
    case Unsaid{why}:
      stopped(M.Good{old}, why, [])

# the sources are read only when an import has a hash to stop naming
def ask.srcs(none: Bool, +rs: List<&2, Reply>) -> Srcs:
  match none:
    case True{}:
      Srcs{[]}
    case False{}:
      sources(rs, Sources{})

def deps.edits(dd: Deps) -> List<&2, U.Swap>:
  Deps{_ds, _ss, es, _m, _sy, _tr, _asks, _bad} = dd
  es

# every pin answered: what is written around the lock
def settled(+rs: List<&2, Reply>, +old: M.Manifest, +dd: Deps, tt: Tools) -> Next:
  got.ignore(text.said(rs, Ignore{}),
    ask.srcs(List.is_empty(&2, U.Swap, deps.edits(dd)), rs), old, dd, tt)

# the pins' questions still open: the lock waits for them
def pins.asks(asks: List<&2, Ask>, +rs: List<&2, Reply>, +old: M.Manifest, dd: Deps, tt: Tools) -> Next:
  match asks:
    case []:
      settled(rs, old, dd, tt)
    case h <> t:
      stopped(M.Good{old}, "ez: the upgrade still has questions for the remote", h <> t)

# a refusal wins over every question still open
def pins.bad(
  clean: Bool,
  +bad: String,
  asks: List<&2, Ask>,
  +rs: List<&2, Reply>,
  +old: M.Manifest,
  dd: Deps,
  tt: Tools
) -> Next:
  match clean:
    case True{}:
      pins.asks(asks, rs, old, dd, tt)
    case False{}:
      stopped(M.Good{old}, bad, [])

# the dependencies' and the tools' answers together
def pins(dd: Deps, tt: Tools, +rs: List<&2, Reply>, +old: M.Manifest) -> Next:
  Deps{ds, ss, es, dm, dsy, dtr, dasks, +dbad} = dd
  Tools{ts, tm, tsy, tasks, +tbad} = tt
  pins.bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
    Bool.pick(String, String.is_empty(dbad), tbad, dbad),
    List.append(&2, Ask, dasks, tasks), rs, old,
    Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Tools{ts, tm, tsy, [], ""})

# `--package` has to name a dependency or a pinned CLI
def known(ok: Bool, +only: String, +rs: List<&2, Reply>, +old: M.Manifest) -> Next:
  match ok:
    case False{}:
      stopped(M.Good{old}, "ez: no dependency or tool named " ++ only, [])
    case True{}:
      M.Manifest{_name, _entry, _bin, +hub, +ds, +ts} = old
      pins(deps.walk(rs, only, M.hub.or(hub), ds), tools.walk(rs, only, ts), rs, old)

# `ez lock --upgrade [--package only]` over the ledger and the answers so far.
# A ledger that does not parse is the plain lock's refusal.
def next(+only: String, read: M.Read, +rs: List<&2, Reply>) -> Next:
  match read:
    case M.Bad{why}:
      plain(M.Bad{why})
    case M.Good{+m}:
      M.Manifest{_name, _entry, _bin, _hub, +ds, +ts} = m
      known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), only, rs, m)
