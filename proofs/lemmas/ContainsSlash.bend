# a string that holds a `/` after a prefix contains `/`
import Base
import ../../src/check/eq.bend as Eq
import ../../laws/HashPathIsHubImport.bend as L1

# LAW: a string that holds a `/` somewhere after a prefix contains `/`
law contains_slash.arm:
  for +h: Char
  for t: String
  for +rest: String
  for b: Bool
  for eb: {b == String.starts_with(SCon{h, String.append(t, SCon{'/', rest})},
    "/") : Bool}
  for ih: {String.contains(String.append(t, SCon{'/', rest}), "/") == True{}
    : Bool}
  {String.contains(SCon{h, String.append(t, SCon{'/', rest})}, "/") == True{}
    : Bool}

def contains_slash.arm(_h, t, rest, b, eb, ih):
  match b:
    case True{}:
      %eb : {String.contains.if(String.append(t, SCon{'/', rest}), "/", _)
        == True{} : Bool}
      {==}
    case False{}:
      %eb : {String.contains.if(String.append(t, SCon{'/', rest}), "/", _)
        == True{} : Bool}
      ih

law contains_slash:
  for s: String
  for +rest: String
  {String.contains(String.append(s, SCon{'/', rest}), "/") == True{} : Bool}

def contains_slash(s, rest):
  match s:
    case SNil{}:
      Equal.trans(Bool,
        String.contains.if(rest, "/", String.starts_with(SCon{'/', rest}, "/")),
        String.contains.if(rest, "/", True{}),
        True{},
        Equal.cong(Bool, Bool,
          x => String.contains.if(rest, "/", x),
          String.starts_with(SCon{'/', rest}, "/"), True{},
          Equal.trans(Bool,
            String.starts_with.go.if("", rest, Char.is_eq('/', '/')),
            String.starts_with.go.if("", rest, True{}),
            True{},
            Equal.cong(Bool, Bool,
              x => String.starts_with.go.if("", rest, x),
              Char.is_eq('/', '/'), True{}, Eq.char_eq_self('/')),
            Eq.starts_nil(rest))),
        {==})
    case SCon{+h, +t}:
      contains_slash.arm(h, t, rest,
        String.starts_with(SCon{h, String.append(t, SCon{'/', rest})}, "/"),
        {==}, contains_slash(t, rest))

def L1.hub_named(h, rest):
  Equal.trans(Bool,
    Bool.and(
      String.starts_with(String.append(String.append("0x", h), SCon{'/', rest}),
        "0x"),
      String.contains(String.append(String.append("0x", h), SCon{'/', rest}),
        "/")),
    Bool.and(True{}, True{}),
    True{},
    Equal.trans(Bool,
      Bool.and(
        String.starts_with(String.append(String.append("0x", h),
          SCon{'/', rest}), "0x"),
        String.contains(String.append(String.append("0x", h), SCon{'/', rest}),
          "/")),
      Bool.and(True{},
        String.contains(String.append(String.append("0x", h), SCon{'/', rest}),
          "/")),
      Bool.and(True{}, True{}),
      Equal.cong(Bool, Bool,
        x => Bool.and(x,
          String.contains(String.append(String.append("0x", h),
            SCon{'/', rest}), "/")),
        String.starts_with(String.append(String.append("0x", h),
          SCon{'/', rest}), "0x"),
        True{},
        Equal.trans(Bool,
          String.starts_with(String.append(String.append("0x", h),
            SCon{'/', rest}), "0x"),
          String.starts_with(String.append("0x",
            String.append(h, SCon{'/', rest})), "0x"),
          True{},
          Equal.cong(String, Bool,
            s => String.starts_with(s, "0x"),
            String.append(String.append("0x", h), SCon{'/', rest}),
            String.append("0x", String.append(h, SCon{'/', rest})),
            Eq.append_assoc("0x", h, SCon{'/', rest})),
          Eq.starts_append("0x", String.append(h, SCon{'/', rest})))),
      Equal.cong(Bool, Bool, x => Bool.and(True{}, x),
        String.contains(String.append(String.append("0x", h), SCon{'/', rest}),
          "/"),
        True{}, contains_slash(String.append("0x", h), rest))),
    {==})
