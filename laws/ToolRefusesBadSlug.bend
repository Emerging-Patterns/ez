# A remote target whose cache slug is empty, absolute, or climbs with `..` is
# refused.
import Base
import ../src/ez/target.bend as Tgt
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# ---------------------------------------------------------------------------
# laws/ToolRefusesBadSlug.bend: the cache slug

# LAW: a remote whose slug is empty, absolute or climbs is no place
law remote_refuses_slug:
  for +url: String
  for +slug: String
  for bad: {Tgt.slug.ok(slug) == False{} : Bool}
  {Tgt.remote(url, slug) == Tgt.Bad{"not a repository"} : Tgt.Place}

# LAW: and a tool command refuses a remote whose slug is not safe, however it
# came by it
law tool_refuses_bad_slug:
  for +w: TW.World
  for +url: String
  for +slug: String
  for pl: {TP.place(w) == Tgt.Remote{url, slug} : Tgt.Place}
  for bad: {Tgt.slug.ok(slug) == False{} : Bool}
  {TP.refuses(w) == True{} : Bool}

# LAW: and a target that names no place
law tool_refuses_nowhere:
  for +w: TW.World
  for +why: String
  for pl: {TP.place(w) == Tgt.Bad{why} : Tgt.Place}
  {TP.refuses(w) == True{} : Bool}
