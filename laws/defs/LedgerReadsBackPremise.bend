# ReadsBack: every ledger Rend.renderable accepts reads back as itself, the
# premise eztoml's round trip gives
import Base
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/add/world.bend as A

# laws/WrittenLedgerReadsBack.bend, as the premise a law takes when it is
# about the file a ledger is written to: every ledger `Rend.renderable`
# accepts reads back, from the text `Rend.show` writes, as itself.
# `Rend.show` is eztoml's `render` of the document ez assembles
# (`Rend.text`), and `M.parse` reads through eztoml's `parse`, so this rests
# on eztoml's round trip (eztoml's laws/RenderThenParse.bend, pending in
# eztoml v0.4.0) and is trusted in src/toml/toml.bend, not proved here. A
# law that takes it holds of the file's bytes wherever the round trip does.
def ReadsBack() -> Type:
  @m:M.Manifest -> {Rend.renderable(m) == True{} : Bool} -> {M.parse(Rend.show(m)) == M.Good{m} : M.Read}
