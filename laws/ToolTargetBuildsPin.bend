# A target naming a `[tools.*]` pin in ez.toml builds the lock's rev, url,
# entry and bin. An `owner/repo` or URL target builds the commit `git
# ls-remote <url> HEAD` names. A path builds its clean `HEAD`. A checkout with
# no ez.toml is a plain Bend repository: it is built with no lock fetched and
# with BEND_LIB at a library of its own under the cache, where bend fetches
# its hub imports. A checkout with an ez.toml and no ez.lock.toml is refused
# when its binary is to be built.
import Base
import ../src/ledger/manifest.bend as M
import ../src/git/git.bend as Git
import ../src/lock/up.bend as Up
import ../src/ez/target.bend as Tgt
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# ---------------------------------------------------------------------------
# laws/ToolTargetBuildsPin.bend: what a target builds

# LAW: a name the project's ledger pins is the pin the lock records under it
law tool_pin_src:
  for +w: TW.World
  for +m: M.Manifest
  for +body: String
  for led: {TW.project(w) == M.Good{m} : M.Read}
  for named: {TP.unpinned(m, TW.target(w)) == False{} : Bool}
  for lock: {TW.lock(w) == Some{body} : Maybe<&2, String>}
  for pinned: {String.is_empty(M.tool.name(TP.pin.in(body, TW.target(w)))) == False{} : Bool}
  {TP.src(w) == TP.Pin{TW.target(w),
    M.source.url(M.tool.source(TP.pin.in(body, TW.target(w)))),
    M.source.rev(M.tool.source(TP.pin.in(body, TW.target(w)))),
    TP.over.of(M.tool.bin(TP.pin.in(body, TW.target(w))),
      M.tool.entry(TP.pin.in(body, TW.target(w))))} : TP.Src}

# LAW: and is built at the lock's rev
law tool_pin_rev:
  for +w: TW.World
  for +n: String
  for +u: String
  for +r: String
  for +o: String
  for s: {TP.src(w) == TP.Pin{n, u, r, o} : TP.Src}
  {TP.rev(w) == r : String}

# LAW: from the lock's url
law tool_pin_url:
  for +w: TW.World
  for +n: String
  for +u: String
  for +r: String
  for +o: String
  for s: {TP.src(w) == TP.Pin{n, u, r, o} : TP.Src}
  {TP.place(w) == TP.place.pin(Tgt.classify(u)) : Tgt.Place}

# LAW: with the file the lock's `bin` or `entry` names
law tool_pin_over:
  for +w: TW.World
  for +n: String
  for +u: String
  for +r: String
  for +o: String
  for s: {TP.src(w) == TP.Pin{n, u, r, o} : TP.Src}
  {TP.over(w) == o : String}

# LAW: a plain repository is built with no lock fetched
law tool_plain_no_lock:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == True{} : Bool}
  {TP.fetches(TP.plan(w)) == False{} : Bool}

# LAW: with BEND_LIB at a library of its own under the cache, beside its
# binaries, for bend to fetch its hub imports into
law tool_plain_lib:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == True{} : Bool}
  {TP.built.lib(TP.plan(w)) == TP.dir(w) ++ "/lib" : String}

# LAW: while an ez project whose checkout has no ez.lock.toml is refused
# when its binary is to be built
law tool_ledger_needs_lock:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == False{} : Bool}
  for none: {TP.co.lock(TP.co(w)) == None{} : Maybe<&2, String>}
  {TP.refuses(w) == True{} : Bool}

# LAW: any other word is a free target, where its word names
law tool_free_src:
  for +w: TW.World
  for +m: M.Manifest
  for led: {TW.project(w) == M.Good{m} : M.Read}
  for free: {TP.unpinned(m, TW.target(w)) == True{} : Bool}
  {TP.src(w) == TP.Free{Tgt.classify(TW.target(w))} : TP.Src}

# LAW: a free remote is built at the commit its HEAD names
law tool_free_rev:
  for +w: TW.World
  for +url: String
  for +slug: String
  for +text: String
  for s: {TP.src(w) == TP.Free{Tgt.Remote{url, slug}} : TP.Src}
  for said: {TP.head.said(w, url) == Up.Said{text} : Up.Said}
  {TP.rev(w) == Git.tip.rev(Git.rows(String.lines(text))) : String}

# LAW: a path is built at the commit git says of it
law tool_path_rev:
  for +w: TW.World
  for +p: String
  for +abs: String
  for +top: String
  for +head: String
  for ok: Bool
  for +status: String
  for s: {TP.src(w) == TP.Free{Tgt.Local{p}} : TP.Src}
  for l: {TP.loc(p, w) == TP.Loc{abs, top, head, ok, status} : TP.Loc}
  {TP.rev(w) == TP.local.rev(abs, top, head, ok, status) : String}

# LAW: which is its HEAD when it is the top of a clean checkout
law local_rev_clean:
  for +abs: String
  for +head: String
  {TP.local.rev(abs, abs, head, True{}, "") == head : String}
