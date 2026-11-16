# proofs of laws/ServeSpeaksHttp.bend
import Base
import ../src/check/serve.bend as S
import ../laws/ServeSpeaksHttp.bend as Laws

def Laws.width_ascii(code, e):
  %e : {Bool.pick(U32, _, 1,
      Bool.pick(U32, U32.is_lt(code, 2048), 2,
        Bool.pick(U32, U32.is_lt(code, 65536), 3, 4))) == 1 : U32}
  {==}

def Laws.size_ascii(ch, tail, e):
  %Equal.sym(U32, S.width(Char.to_u32(ch)), 1, Laws.width_ascii(Char.to_u32(ch), e))
    : {U32.add(_, S.size(tail)) == U32.add(1, S.size(tail)) : U32}
  {==}

def Laws.at_first(_word, _rest):
  {==}

def Laws.at_next(_word, _rest, _index):
  {==}

def Laws.at_past(index):
  match index:
    case 0n:
      {==}
    case 1n+_p:
      {==}

def Laws.cut_blank(_lines):
  {==}

def Laws.cut_cr(_lines):
  {==}

def Laws.cut_line(line, lines, e):
  %e : {S.cut.step(_, lines, _u => S.cut.put(line, S.cut(lines)))
    == S.cut.put(line, S.cut(lines)) : S.Msg}
  {==}

def Laws.empty_head_partial(_body):
  {==}

def Laws.clen_skip(line, lines, e):
  %e : {Bool.pick(U32, _,
      Maybe.default(&2, U32, U32.read(String.trim(String.drop(line, 15n))), 0),
      S.clen(lines)) == S.clen(lines) : U32}
  {==}

def Laws.clen_read(line, lines, e):
  %e : {Bool.pick(U32, _,
      Maybe.default(&2, U32, U32.read(String.trim(String.drop(line, 15n))), 0),
      S.clen(lines))
    == Maybe.default(&2, U32, U32.read(String.trim(String.drop(line, 15n))), 0) : U32}
  {==}

def Laws.response_frames(_status, _body):
  {==}
