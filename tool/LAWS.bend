# tool: the laws. The human states them; PROOF.bend must prove them. They are
# stated over the plan `ez tool run`, `install` and `upgrade` run
# (tool/plan.bend), over what it resolves a target to, and over the words
# `ez tool run` and `ez run` hand on (ez/args.bend), so what they say of the
# plan is what the command does, the interpreter's faithfulness being
# EZ-TRUST-2.
import Base
import ./world.bend as TW
import ./plan.bend as TP
import ../lock/plan.bend as P
import ../lock/up.bend as Up
import ../manifest/manifest.bend as M
import ../git/git.bend as Git
import ../pkg/path.bend as Path
import ../ez/target.bend as Tgt
import ../ez/args.bend as Args

# ---------------------------------------------------------------------------
# refusals

# LAW: a tool command that refuses writes nothing: no checkout laid under the
# cache, no binary built, no link. Its plan has no effect at all.
# EZ-OUT-2
law tool_refusal_writes_nothing:
  for +w: TW.World
  for r: {TP.refuses(w) == True{} : Bool}
  {TP.writes(TP.plan(w)) == False{} : Bool}

# LAW: `ez tool sync` that refuses installs nothing
# EZ-OUT-2
law sync_refusal_installs_nothing:
  for +ledger: Maybe<&2, String>
  for +lock: Maybe<&2, String>
  for r: {TP.sync.refuses(TP.sync(ledger, lock)) == True{} : Bool}
  {TP.sync.names(TP.sync(ledger, lock)) == [] : List<&2, String>}

# ---------------------------------------------------------------------------
# EZ-TOOL-1: the link directory

# LAW: `$EZ_TOOL_BIN`, when it is set
# EZ-TOOL-1
law bin_dir_ez:
  for +ez: String
  for +xdg: String
  for +home: String
  for ne: {False{} == String.is_empty(ez) : Bool}
  {TW.bin.dir(ez, xdg, home) == Some{ez} : Maybe<&2, String>}

# LAW: otherwise `$XDG_BIN_HOME`, when it is set
# EZ-TOOL-1
law bin_dir_xdg:
  for +xdg: String
  for +home: String
  for ne: {False{} == String.is_empty(xdg) : Bool}
  {TW.bin.dir("", xdg, home) == Some{xdg} : Maybe<&2, String>}

# LAW: otherwise `$HOME/.local/bin`
# EZ-TOOL-1
law bin_dir_home:
  for +home: String
  for ne: {False{} == String.is_empty(home) : Bool}
  {TW.bin.dir("", "", home) == Some{home ++ "/.local/bin"} : Maybe<&2, String>}

# LAW: and nowhere when all three are empty
# EZ-TOOL-1
law bin_dir_none:
  for +cache: String
  for +path: String
  {TW.bin.of(TW.Env{"", "", cache, "", path}) == None{} : Maybe<&2, String>}

# LAW: `install` and `upgrade` link into that directory, under the name
# the checkout gives its package
# EZ-TOOL-1
law tool_links_in_bin_dir:
  for +w: TW.World
  for a: TW.Act
  for +d: String
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for got: {TW.bin.of(TW.env(w)) == Some{d} : Maybe<&2, String>}
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.link.at(TP.plan(w)) == d ++ "/" ++ TP.name(w) : String}

# LAW: and refuse, before anything is built, when there is none
# EZ-TOOL-1
law tool_needs_bin_dir:
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for none: {TW.bin.of(TW.env(w)) == None{} : Maybe<&2, String>}
  {TP.refuses(w) == True{} : Bool}

# ---------------------------------------------------------------------------
# EZ-TOOL-2: the binary's record, in the plan

# LAW: a binary that is there, with this record, is not built again
# EZ-TOOL-2
law tool_reuses_record:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for hit: {TP.reuse(w) == True{} : Bool}
  {TP.builds(TP.plan(w)) == False{} : Bool}

# LAW: any other is built
# EZ-TOOL-2
law tool_builds_on_miss:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.builds(TP.plan(w)) == True{} : Bool}

# ---------------------------------------------------------------------------
# EZ-TOOL-3: a local target that is no commit

# LAW: a path `git status` names anything in is no commit
# EZ-TOOL-3
law local_rev_dirty:
  for +abs: String
  for +top: String
  for +head: String
  for ok: Bool
  for +status: String
  for d: {False{} == String.is_empty(status) : Bool}
  {TP.local.rev(abs, top, head, ok, status) == "" : String}

# LAW: nor is one `git status` did not answer for, which is not a checkout
# EZ-TOOL-3
law local_rev_unchecked:
  for +abs: String
  for +top: String
  for +head: String
  for +status: String
  {TP.local.rev(abs, top, head, False{}, status) == "" : String}

# LAW: nor is one that is not the top of its checkout
# EZ-TOOL-3
law local_rev_elsewhere:
  for +abs: String
  for +top: String
  for +head: String
  for ok: Bool
  for +status: String
  for e: {False{} == String.eq(top, abs) : Bool}
  {TP.local.rev(abs, top, head, ok, status) == "" : String}

# LAW: a target with no commit is built on every run
# EZ-TOOL-3
law tool_unrevved_builds:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for none: {TP.rev(w) == "" : String}
  {TP.builds(TP.plan(w)) == True{} : Bool}

# ---------------------------------------------------------------------------
# EZ-TOOL-4: what a target builds

# LAW: a name the project's ledger pins is the pin the lock records under it
# EZ-TOOL-4
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
# EZ-TOOL-4
law tool_pin_rev:
  for +w: TW.World
  for +n: String
  for +u: String
  for +r: String
  for +o: String
  for s: {TP.src(w) == TP.Pin{n, u, r, o} : TP.Src}
  {TP.rev(w) == r : String}

# LAW: from the lock's url
# EZ-TOOL-4
law tool_pin_url:
  for +w: TW.World
  for +n: String
  for +u: String
  for +r: String
  for +o: String
  for s: {TP.src(w) == TP.Pin{n, u, r, o} : TP.Src}
  {TP.place(w) == TP.place.pin(Tgt.classify(u)) : Tgt.Place}

# LAW: with the file the lock's `bin` or `entry` names
# EZ-TOOL-4
law tool_pin_over:
  for +w: TW.World
  for +n: String
  for +u: String
  for +r: String
  for +o: String
  for s: {TP.src(w) == TP.Pin{n, u, r, o} : TP.Src}
  {TP.over(w) == o : String}

# LAW: any other word is a free target, where its word names
# EZ-TOOL-4
law tool_free_src:
  for +w: TW.World
  for +m: M.Manifest
  for led: {TW.project(w) == M.Good{m} : M.Read}
  for free: {TP.unpinned(m, TW.target(w)) == True{} : Bool}
  {TP.src(w) == TP.Free{Tgt.classify(TW.target(w))} : TP.Src}

# LAW: a free remote is built at the commit its HEAD names
# EZ-TOOL-4
law tool_free_rev:
  for +w: TW.World
  for +url: String
  for +slug: String
  for +text: String
  for s: {TP.src(w) == TP.Free{Tgt.Remote{url, slug}} : TP.Src}
  for said: {TP.head.said(w, url) == Up.Said{text} : Up.Said}
  {TP.rev(w) == Git.tip.rev(Git.rows(String.lines(text))) : String}

# LAW: a path is built at the commit git says of it
# EZ-TOOL-4
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
# EZ-TOOL-4
law local_rev_clean:
  for +abs: String
  for +head: String
  {TP.local.rev(abs, abs, head, True{}, "") == head : String}

# ---------------------------------------------------------------------------
# EZ-TOOL-5 and EZ-TOOL-6: the program

# LAW: `ez tool run` that does not refuse ends by starting the program with
# the words it was given, as the last thing, so its status is the command's
# EZ-TOOL-5
law tool_run_exits_with_program:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.exit(TP.plan(w)) == TP.Exits{TP.out(w), args} : TP.Exit}

# LAW: a tool command that refuses exits 1 and starts nothing
# EZ-TOOL-5
law tool_refusal_exits_one:
  for +w: TW.World
  for r: {TP.refuses(w) == True{} : Bool}
  {TP.exit(TP.plan(w)) == TP.Refusal{} : TP.Exit}

# LAW: `install` and `upgrade` never start the program, whatever the World
# EZ-TOOL-6
law tool_link_never_runs:
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.launches(TP.plan(w)) == False{} : Bool}

# ---------------------------------------------------------------------------
# EZ-OUT-1: the status a tool command exits with. The interpreter exits with
# `TP.code` of the plan's end and the status of the program it started, 0
# when it started none.

# LAW: a tool command that refuses exits 1, whatever a program would have
# exited with, since it starts none
# EZ-OUT-1
law tool_refusal_status_one:
  for +w: TW.World
  for s: U32
  for r: {TP.refuses(w) == True{} : Bool}
  {TP.code(TP.exit(TP.plan(w)), s) == 1 : U32}

# LAW: `ez tool run` that does not refuse exits with the program's status
# EZ-OUT-1
law tool_run_status_is_program:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  for ok: {TP.refuses(w) == False{} : Bool}
  for s: U32
  {TP.code(TP.exit(TP.plan(w)), s) == s : U32}

# LAW: `install` and `upgrade` that do not refuse exit 0
# EZ-OUT-1
law tool_link_status_zero:
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for ok: {TP.refuses(w) == False{} : Bool}
  for s: U32
  {TP.code(TP.exit(TP.plan(w)), s) == 0 : U32}

# LAW: `ez tool sync` ends with 1 exactly when it refuses, and 0 when it
# does not. Each install it runs ends as `ez tool install` does, so one that
# refuses ends the sync there with 1.
# EZ-OUT-1
law sync_exits_as_it_refuses:
  for +ledger: Maybe<&2, String>
  for +lock: Maybe<&2, String>
  {P.status(TP.sync.outcome(TP.sync(ledger, lock)))
    == P.status.of(TP.sync.refuses(TP.sync(ledger, lock))) : U32}

# LAW: with no ez.toml, `ez tool sync` refuses, whatever the lock says, so
# it installs nothing and exits 1
# EZ-OUT-1
law sync_needs_ledger:
  for +lock: Maybe<&2, String>
  {TP.sync.refuses(TP.sync(None{}, lock)) == True{} : Bool}

# ---------------------------------------------------------------------------
# EZ-TOOL-7: the file built and the link's name

# LAW: the pin's `bin` first
# EZ-TOOL-7
law file_pin_bin:
  for +pb: String
  for +pe: String
  for +b: String
  for +e: String
  for +ne: {False{} == String.is_empty(pb) : Bool}
  {TP.chosen(TP.over.of(pb, pe), b, e) == pb : String}

# LAW: then the pin's `entry`
# EZ-TOOL-7
law file_pin_entry:
  for +pe: String
  for +b: String
  for +e: String
  for ne: {False{} == String.is_empty(pe) : Bool}
  {TP.chosen(TP.over.of("", pe), b, e) == pe : String}

# LAW: then the checkout's `bin`
# EZ-TOOL-7
law file_bin:
  for +b: String
  for +e: String
  for ne: {False{} == String.is_empty(b) : Bool}
  {TP.chosen("", b, e) == b : String}

# LAW: then its `entry`
# EZ-TOOL-7
law file_entry:
  for +e: String
  for ne: {False{} == String.is_empty(e) : Bool}
  {TP.chosen("", "", e) == e : String}

# LAW: then `main.bend`
# EZ-TOOL-7
law file_main:
  for +o: String
  for +b: String
  for +e: String
  for zo: {String.is_empty(o) == True{} : Bool}
  for zb: {String.is_empty(b) == True{} : Bool}
  for ze: {String.is_empty(e) == True{} : Bool}
  {TP.chosen(o, b, e) == "main.bend" : String}

# LAW: a build builds that file of the checkout
# EZ-TOOL-7
law tool_builds_file:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.built(TP.plan(w))
    == Path.join(TP.top(w), TP.chosen(TP.over(w), TP.bin(w), TP.entry(w))) : String}

# LAW: the link is named after the package
# EZ-TOOL-7
law out_name_own:
  for +n: String
  for ne: {False{} == String.is_empty(n) : Bool}
  {Tgt.out.name(n) == n : String}

# LAW: or `app`, when the checkout names none
# EZ-TOOL-7
law out_name_app:
  for +n: String
  for z: {String.is_empty(n) == True{} : Bool}
  {Tgt.out.name(n) == "app" : String}

# LAW: and an install or upgrade links under that name
# EZ-TOOL-7
law tool_links_named:
  for +w: TW.World
  for a: TW.Act
  for +d: String
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for got: {TW.bin.of(TW.env(w)) == Some{d} : Maybe<&2, String>}
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.link.at(TP.plan(w)) == d ++ "/" ++ Tgt.out.name(TP.name.raw(w)) : String}

# LAW: a package name that is not a TOML bare key, which could climb out of
# the link directory or the cache, is refused
# EZ-TOOL-7
law tool_refuses_unsafe_name:
  for +w: TW.World
  for bad: {TP.name.ok(TP.name.raw(w)) == False{} : Bool}
  {TP.refuses(w) == True{} : Bool}

# ---------------------------------------------------------------------------
# EZ-TOOL-8: the cache slug

# LAW: a remote whose slug is empty, absolute or climbs is no place
# EZ-TOOL-8
law remote_refuses_slug:
  for +url: String
  for +slug: String
  for bad: {Tgt.slug.ok(slug) == False{} : Bool}
  {Tgt.remote(url, slug) == Tgt.Bad{"not a repository"} : Tgt.Place}

# LAW: and a tool command refuses a remote whose slug is not safe, however it
# came by it
# EZ-TOOL-8
law tool_refuses_bad_slug:
  for +w: TW.World
  for +url: String
  for +slug: String
  for pl: {TP.place(w) == Tgt.Remote{url, slug} : Tgt.Place}
  for bad: {Tgt.slug.ok(slug) == False{} : Bool}
  {TP.refuses(w) == True{} : Bool}

# LAW: and a target that names no place
# EZ-TOOL-8
law tool_refuses_nowhere:
  for +w: TW.World
  for +why: String
  for pl: {TP.place(w) == Tgt.Bad{why} : Tgt.Place}
  {TP.refuses(w) == True{} : Bool}

# ---------------------------------------------------------------------------
# EZ-TOOL-9: the words handed on

# LAW: `ez tool run <target> -- <words>` hands on the words after `--`
# EZ-TOOL-9
law tool_rest_dash:
  for +a: String
  for +b: String
  for +t: String
  for +ws: List<&2, String>
  {Args.tool.rest(a <> (b <> (t <> ("--" <> ws)))) == ws : List<&2, String>}

# LAW: and every word after the target when the first is not `--`
# EZ-TOOL-9
law tool_rest_word:
  for +a: String
  for +b: String
  for +t: String
  for +h: String
  for +ws: List<&2, String>
  for ne: {False{} == String.eq(h, "--") : Bool}
  {Args.tool.rest(a <> (b <> (t <> (h <> ws)))) == h <> ws : List<&2, String>}

# LAW: and none when there are none
# EZ-TOOL-9
law tool_rest_none:
  for +a: String
  for +b: String
  for +t: String
  {Args.tool.rest(a <> (b <> (t <> []))) == [] : List<&2, String>}

# LAW: which the program is started with
# EZ-TOOL-9
law tool_run_passes_words:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.exit(TP.plan(w)) == TP.Exits{TP.out(w), args} : TP.Exit}

# LAW: `ez run` hands the entry every word after `run`
# EZ-TOOL-9
law run_line_rest:
  for +e: String
  for +a: String
  for +ws: List<&2, String>
  {Args.run.line(e, a <> ws) == "bend" <> (e <> ws) : List<&2, String>}
