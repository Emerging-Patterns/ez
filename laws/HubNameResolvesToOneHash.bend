# A named import `<name>@<version>/...` resolves to one hash: the one the
# ledger the lock is made from records for that name (ez.toml, or in a
# workspace the joint ledger, which records every member imported by name,
# laws/PublishedMemberImportedByName.bend), else the one the lock being
# rewritten records, else the one the hub answers. The lock walks that
# package, records the pair under `[names]`, and `ez fetch` lays that hash
# in the name's file. `ez add <name>@<version>` asks the hub the ledger
# names, and records the name with the hash the hub answers.
#
# also rests on: laws/LedgerNamesFirst.bend
#
# laws/HubNameResolvesToOneHash.bend to laws/NameFilesLaid.bend are proved
# over the package walk, the lock planner, and the plans `ez fetch` and `ez
# doctor` run. A named import is one whose first path segment holds `@` with
# a `/` after it, as bend reads it; the walk queues no file for it
# (`named_is_no_module`) and stops, in bend's words, on a name bend would
# refuse (`unnamed_stops`, `unnamed_refused`). The lock resolves a name by a
# table: the names ez.toml records, each with the `hash` beside it, first
# (`ledger_names_first`), then the names the lock being rewritten records
# (`lock_answer_names`), then the hub's answers to `GET
# $BEND_HUB/name/<name>@<version>`. A name the table already resolves is
# never put to the hub (`resolved_not_asked`). The walk queues the package
# the table gives a name (`named_kid_queued`), the lock records each name
# with that hash (`lock_names_agree`), and `[names]` reads back as rendered
# (trusted in src/lock/lock.bend). A lock that is made lays the names file
# of every name it records (`lock_lays_its_names`); `ez fetch` lays the
# lock's hash in a missing file and over one that names another hash,
# refuses a name bend would not read back, and lays no other
# (`fetch_names_the_lock`, `fetch_lays_missing_name`, `fetch_rewrites_name`,
# `fetch_refuses_unread_name`, `fetch_lays_the_names`); and `ez doctor`
# fails when a file is missing or names another hash
# (`doctor_wrong_name_fails`). A named import in the project's own files
# must be an ez.toml dependency, or `ez lock` refuses and says so; `ez
# doctor` reads named imports as import lines for
# laws/DoctorReportsDrift.bend too. `ez lock --upgrade` leaves named
# dependencies as they are, and rewriting import lines stays about `0x`
# hashes. `ez add <name>@<version>` asks the hub the ledger names for the
# name, then for the package (`add_named_asks_hub`), records the name with
# the hash the hub answered (`add_named_records_name`), so the next `ez
# lock` reads the pair from ez.toml and puts nothing to the hub, and lays
# the name's file (`add_named_lays_name`). That a name the hub answered once
# keeps its hash is trusted in src/lock/lock.bend; that the interpreter
# writes a names file as `0x<hash>` and a newline, and reads one as it is on
# disk, is trusted in src/ez/app.bend.
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/hub.bend as H
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# whether every name of a list is recorded with the hash a table gives it.
# Law vocabulary.
def names.agree(+ns: List<&2, L.Name>, ps: List<&2, L.Name>) -> Bool:
  match ps:
    case []:
      True{}
    case L.Name{+n, h} <> t:
      +rest = names.agree(ns, t)
      Bool.and(String.eq(L.name.find(ns, n), h), rest)

# LAW: a package's named import queues the package the table gives its name,
# so the walk reaches, and checks against its manifest, the hash the name
# resolves to
law named_kid_queued:
  for +ns: List<&2, L.Name>
  for +nvs: List<&2, String>
  for +nv: String
  for e: {L.seen.holds(nvs, nv) == True{} : Bool}
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  {L.seen.holds(L.name.hashes(ns, nvs), L.name.find(ns, nv)) == True{} : Bool}

# LAW: and every name the lock records, it records with the hash the table
# gives it, the same hash
law lock_names_agree:
  for +ns: List<&2, L.Name>
  for nvs: List<&2, String>
  {names.agree(ns, L.name.pairs(ns, nvs)) == True{} : Bool}

# LAW: the dependency recorded is the name as it was given, under `hub`,
# with the hash the hub answered for it, so the ledger names that name to
# that hash, and the next `ez lock` reads the pair from the ledger without
# asking the hub (laws/ResolvedNotAsked.bend)
law add_named_records_name:
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  for +ok: {H.refuses(w) == False{} : Bool}
  {H.added(w) == M.Dep{H.key(w), String.trim(text), M.dep.entry(H.added(w)),
    M.Hub{A.target(w)}} : M.Dep}

# LAW: every question the add asks names the hub the ledger names
law add_named_asks_hub:
  for +w: A.World
  {H.asks.hub(H.wants(w), A.hub(w)) == True{} : Bool}

# Names. Every name the lock records has its file under BEND_LIB, the file
# bend reads the name's hash from before it would ask the hub. `FP.name.part`
# is where one name stands: its file still to read, kept, to lay (with the
# hash the file there held), or a refusal.

# whether a name's part lays the name with this hash, when it lays it. Law
# vocabulary.
def put.agrees(+nv: String, +hash: String, part: FP.Nm) -> Bool:
  match part:
    case FP.NmPut{n, h, _was}:
      Bool.and(String.eq(n, nv), String.eq(h, hash))
    case _:
      True{}

# LAW: a names file `ez fetch` lays for a name holds the hash the lock
# records for that name
law fetch_names_the_lock:
  for +rs: List<&2, F.Reply>
  for +nv: String
  for +hash: String
  {put.agrees(nv, hash, FP.name.part(rs, L.Name{nv, hash})) == True{} : Bool}
