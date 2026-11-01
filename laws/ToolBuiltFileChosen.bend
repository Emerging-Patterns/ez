# The built file is the pin's `bin`, then the pin's `entry`, then the file
# `--entry` names, then the checkout's `bin`, then its `entry`, then
# `main.bend`, and a built file that is not in the checkout is refused. The
# link is named after the checkout's package name, or `app`; a plain
# repository's is the built file's name without `.bend`, or the repository's
# name when that is `main`; and a name that is not a TOML bare key is refused.
import Base
import ../src/pkg/path.bend as Path
import ../src/ez/target.bend as Tgt
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# ---------------------------------------------------------------------------
# laws/ToolBuiltFileChosen.bend: the file built and the link's name

# LAW: the pin's `bin` first
law file_pin_bin:
  for +pb: String
  for +pe: String
  for +b: String
  for +e: String
  for +ne: {False{} == String.is_empty(pb) : Bool}
  {TP.chosen(TP.over.of(pb, pe), b, e) == pb : String}

# LAW: then the pin's `entry`
law file_pin_entry:
  for +pe: String
  for +b: String
  for +e: String
  for ne: {False{} == String.is_empty(pe) : Bool}
  {TP.chosen(TP.over.of("", pe), b, e) == pe : String}

# LAW: then the checkout's `bin`
law file_bin:
  for +b: String
  for +e: String
  for ne: {False{} == String.is_empty(b) : Bool}
  {TP.chosen("", b, e) == b : String}

# LAW: then its `entry`
law file_entry:
  for +e: String
  for ne: {False{} == String.is_empty(e) : Bool}
  {TP.chosen("", "", e) == e : String}

# LAW: then `main.bend`
law file_main:
  for +o: String
  for +b: String
  for +e: String
  for zo: {String.is_empty(o) == True{} : Bool}
  for zb: {String.is_empty(b) == True{} : Bool}
  for ze: {String.is_empty(e) == True{} : Bool}
  {TP.chosen(o, b, e) == "main.bend" : String}

# LAW: a build builds that file of the checkout
law tool_builds_file:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.built(TP.plan(w))
    == Path.join(TP.top(w), TP.chosen(TP.wish(TP.over(w), TW.want(w)), TP.bin(w), TP.entry(w)))
    : String}

# LAW: `--entry` wins over the checkout's `bin` and `entry`, as cargo's
# `--bin` wins over Cargo.toml
law file_flag_over_ledger:
  for +f: String
  for +b: String
  for +e: String
  for ne: {False{} == String.is_empty(f) : Bool}
  {TP.chosen(TP.wish("", f), b, e) == f : String}

# LAW: and a pin's `bin` or `entry` wins over `--entry`, since the project
# decided it
law file_pin_over_flag:
  for +o: String
  for +f: String
  for +b: String
  for +e: String
  for +ne: {False{} == String.is_empty(o) : Bool}
  {TP.chosen(TP.wish(o, f), b, e) == o : String}

# LAW: a checkout with no ez.toml is a plain Bend repository, and a build of
# one that no pin names a file for builds its `main.bend`
law tool_plain_builds_main:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == True{} : Bool}
  for free: {TP.over(w) == "" : String}
  for flag: {TW.want(w) == "" : String}
  {TP.built(TP.plan(w)) == Path.join(TP.top(w), "main.bend") : String}

# LAW: or the file `--entry` names
law tool_plain_builds_entry:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  for p: {TP.plain(w) == True{} : Bool}
  for free: {TP.over(w) == "" : String}
  for ne: {False{} == String.is_empty(TW.want(w)) : Bool}
  {TP.built(TP.plan(w)) == Path.join(TP.top(w), TW.want(w)) : String}

# LAW: a file to build that is not in the checkout is refused
law tool_refuses_missing_entry:
  for +w: TW.World
  for miss: {TP.present(w) == False{} : Bool}
  {TP.refuses(w) == True{} : Bool}

# LAW: a plain repository is linked under the stem of the file built
law plain_name_stem:
  for +f: String
  for +u: String
  for ne: {False{} == String.eq(TP.stem(f), "main") : Bool}
  {TP.plain.name(f, u) == TP.stem(f) : String}

# LAW: or under the repository's name, when that stem is `main`
law plain_name_repo:
  for +f: String
  for +u: String
  for m: {True{} == String.eq(TP.stem(f), "main") : Bool}
  {TP.plain.name(f, u) == TP.repo.name(u) : String}

# LAW: which is the name a plain repository's binary and link are given
law tool_plain_named:
  for +w: TW.World
  for p: {TP.plain(w) == True{} : Bool}
  {TP.name.raw(w) == TP.plain.name(TP.choice(w), TP.origin(w)) : String}

# LAW: the link is named after the package
law out_name_own:
  for +n: String
  for ne: {False{} == String.is_empty(n) : Bool}
  {Tgt.out.name(n) == n : String}

# LAW: or `app`, when the checkout names none
law out_name_app:
  for +n: String
  for z: {String.is_empty(n) == True{} : Bool}
  {Tgt.out.name(n) == "app" : String}

# LAW: and an install or upgrade links under that name
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
law tool_refuses_unsafe_name:
  for +w: TW.World
  for bad: {TP.name.ok(TP.name.raw(w)) == False{} : Bool}
  {TP.refuses(w) == True{} : Bool}
