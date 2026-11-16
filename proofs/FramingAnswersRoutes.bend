# proofs of laws/FramingAnswersRoutes.bend
import Base
import ../src/check/serve.bend as S
import ../src/check/framing.bend as F
import ../laws/FramingAnswersRoutes.bend as Laws

def Laws.reply_plain(path, is_plain):
  %is_plain : {F.reply.plain(_, path) == S.response("200 OK", F.plain()) : String}
  {==}

def Laws.reply_chunked(path, not_plain, is_chunked):
  %not_plain : {F.reply.plain(_, path) == F.chunked() : String}
  %is_chunked : {F.reply.chunked(_, path) == F.chunked() : String}
  {==}

def Laws.reply_root(path, not_plain, not_chunked, is_root):
  %not_plain : {F.reply.plain(_, path) == S.response("200 OK", "ok") : String}
  %not_chunked : {F.reply.chunked(_, path) == S.response("200 OK", "ok") : String}
  %is_root : {F.reply.root(_) == S.response("200 OK", "ok") : String}
  {==}

def Laws.reply_unknown(path, not_plain, not_chunked, not_root):
  %not_plain : {F.reply.plain(_, path) == S.response("404 Not Found", "") : String}
  %not_chunked : {F.reply.chunked(_, path) == S.response("404 Not Found", "") : String}
  %not_root : {F.reply.root(_) == S.response("404 Not Found", "") : String}
  {==}

def Laws.chunk_frames(_text):
  {==}

def Laws.hex_one_digit(len, small):
  %small : {Bool.pick(String, _, F.hex.digit(len),
      F.hex.digit(U32.div(len, 16)) ++ F.hex.digit(U32.mod(len, 16))) == F.hex.digit(len) : String}
  {==}

def Laws.hex_two_digits(len, big):
  %big : {Bool.pick(String, _, F.hex.digit(len),
      F.hex.digit(U32.div(len, 16)) ++ F.hex.digit(U32.mod(len, 16)))
    == F.hex.digit(U32.div(len, 16)) ++ F.hex.digit(U32.mod(len, 16)) : String}
  {==}
