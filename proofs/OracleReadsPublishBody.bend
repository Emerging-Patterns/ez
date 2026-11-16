# proofs of laws/OracleReadsPublishBody.bend
import Base
import ../src/check/serve.bend as S
import ../src/check/body.bend as B
import ../laws/OracleReadsPublishBody.bend as Laws

def Laws.ws_skips(ch, tail, space):
  %space : {B.ws.step(_, ch, tail, _u => B.ws(tail)) == B.ws(tail) : String}
  {==}

def Laws.ws_stops(ch, tail, solid):
  %solid : {B.ws.step(_, ch, tail, _u => B.ws(tail)) == SCon{ch, tail} : String}
  {==}

def Laws.eat_hit(text, _ch, heads):
  %heads : {B.eat.at(_, String.drop(text, 1n)) == Some{String.drop(text, 1n)} : Maybe<&2, String>}
  {==}

def Laws.eat_miss(text, _ch, absent):
  %absent : {B.eat.at(_, String.drop(text, 1n)) == None{} : Maybe<&2, String>}
  {==}

def Laws.unesc_empty(fuel):
  match fuel:
    case 0n:
      {==}
    case 1n+_f:
      {==}

def Laws.unesc_plain(fuel, ch, tail, plain):
  %plain : {B.uns.put(B.uns.step(_, ch, tail), B.unesc(fuel, B.uns.rest(B.uns.step(_, ch, tail))))
    == B.uns.push(ch, B.unesc(fuel, tail)) : B.Uns}
  {==}

def Laws.parse_not_object(body, open):
  %open : {B.parse.open(U32.to_nat(U32.add(U32.div(S.size(body), 6), 8)), _)
    == B.OBad{"a body that is not an object"} : B.Obj}
  {==}

def Laws.sorted_one(_entry):
  {==}
