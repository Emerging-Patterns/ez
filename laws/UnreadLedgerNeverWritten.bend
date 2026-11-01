# A ledger that does not parse is never read into a model, and renders as
# nothing, so no command writes a guess over it.
import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/remove/plan.bend as RP

# LAW: and a document with any problem at all is never read into a ledger. It
# comes back as the problem, so no command can go on with a half-read file.
law read_refuses_a_problem:
  for +bad: String
  for +ss: List<&2, T.Sect>
  for e: {False{} == String.is_empty(M.problem(bad, M.missing(ss))) : Bool}
  {M.read(bad, ss) == M.Bad{M.problem(bad, M.missing(ss))} : M.Read}

# LAW: a ledger that did not read renders as nothing. `ez add` and `ez remove`
# write what they render, so a failed read that rendered a guess would
# overwrite a good file with it.
law render_of_unread_is_blank:
  for why: String
  {Rend.render(M.Bad{why}) == "" : String}

# LAW: and a ledger that does not parse is refused the same way, so no lock
# is made from a guess
law lock_refuses_unread:
  for up: Bool
  for +only: String
  for here: String
  for +s: String
  for listing: W.Listing
  for rs: List<&2, W.Reply>
  for us: List<&2, Up.Reply>
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {P.refuses(W.World{W.Args{up, only, here}, Some{s}, listing, rs, us}) == True{} : Bool}

# LAW: a ledger that does not parse is refused, so `ez add` writes no guess
# over it
law add_refuses_unread:
  for +a: A.Args
  for +here: String
  for +home: String
  for +s: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {AP.refuses.command(A.World{a, here, home, Some{s}, ignore, rs, hs}) == True{} : Bool}

# LAW: a ledger that does not parse is refused, so `ez remove` writes no
# guess over it
law remove_refuses_unread:
  for +name: String
  for +s: String
  for +ignore: String
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {RP.refuses(RP.World{name, Some{s}, ignore}) == True{} : Bool}
