# The link directory is `$EZ_TOOL_BIN`, else `$XDG_BIN_HOME`, else
# `$HOME/.local/bin`, an empty value counting as unset. `ez tool install` and
# `ez tool upgrade` link there, and refuse before anything is built when all
# three are empty.
#
# laws/ToolBinDirChosen.bend to laws/RunPassesWords.bend are proved over the
# plan `ez tool run`, `install` and `upgrade` run (`src/tool/plan.bend`),
# over what it resolves a target to, and over the words `ez tool run` and
# `ez run` hand on (`src/share/args.bend`). `ez run` starts bend on the
# entry ez.toml names, or `main.bend` when it names none, with every word
# after `run` (`run_starts_entry`, `run_starts_main`), a line
# `src/ez/start.bend` decides from the ledger the interpreter read and the
# words it was given. What the laws take from the interpreter is trusted in
# src/ez/app.bend: that it asks `git status` with
# `--untracked-files=normal`, so an untracked file counts whatever the
# repository hides; that it reads the real path, the checkout's top and HEAD
# as git gives them; that it starts the program last and exits with its
# status, and exits 1 when a fetch, build or link it runs fails; and that
# `ez tool run` and `ez run` are handed the words the runtime passes them
# (`Args.tool.rest` and `Args.run.line` over `IO.args()` with the program's
# own name, which bend 2.0.32 and later put first, dropped by `Args.all`;
# which words those are is trusted in src/share/args.bend, so a runtime option
# meant for the program `ez tool run` starts goes after a `--RTS`, as in `ez
# tool run <target> --RTS +RTS --gpu off -RTS`), and `ez run`'s line run
# with the project's BEND_LIB in front of it (`Env.line`); and that a build
# runs bend with the library the plan names as BEND_LIB, so a plain
# repository's hub imports are fetched there by bend, which checks each
# against its name.
import Base
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# ---------------------------------------------------------------------------
# laws/ToolBinDirChosen.bend: the link directory

# LAW: `$EZ_TOOL_BIN`, when it is set
law bin_dir_ez:
  for +ez: String
  for +xdg: String
  for +home: String
  for ne: {False{} == String.is_empty(ez) : Bool}
  {TW.bin.dir(ez, xdg, home) == Some{ez} : Maybe<&2, String>}

# LAW: otherwise `$XDG_BIN_HOME`, when it is set
law bin_dir_xdg:
  for +xdg: String
  for +home: String
  for ne: {False{} == String.is_empty(xdg) : Bool}
  {TW.bin.dir("", xdg, home) == Some{xdg} : Maybe<&2, String>}

# LAW: otherwise `$HOME/.local/bin`
law bin_dir_home:
  for +home: String
  for ne: {False{} == String.is_empty(home) : Bool}
  {TW.bin.dir("", "", home) == Some{home ++ "/.local/bin"} : Maybe<&2, String>}

# LAW: and nowhere when all three are empty
law bin_dir_none:
  for +cache: String
  for +path: String
  {TW.bin.of(TW.Env{"", "", cache, "", path}) == None{} : Maybe<&2, String>}

# LAW: `install` and `upgrade` link into that directory, under the name
# the checkout gives its package
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
law tool_needs_bin_dir:
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for none: {TW.bin.of(TW.env(w)) == None{} : Maybe<&2, String>}
  {TP.refuses(w) == True{} : Bool}
