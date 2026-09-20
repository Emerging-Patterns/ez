# Drops bend's check report from a run's output, so only what the program
# printed is compared against a test's `#|` trailer.
#
# 2.0.16 says "All terms check, with N unsafe annotations." on one line. 2.0.18
# says "All terms check, but N defs rely on unsafe or foreign code:" and then a
# `- <name>` line each. Both go; a test asserting its own output never starts a
# line with "- ".
#
# bend also nags about a newer release ("bend 2.0.21 is available: run bend
# update") whenever one exists and the network is up. That is not the program's
# output either, and leaving it in fails every test in the tree the day upstream
# cuts a release.
/^All terms check/                        { report = 1; next }
report && /^- /                           { next }
/^bend .* is available: run bend update$/ { next }
                                          { report = 0; print }
