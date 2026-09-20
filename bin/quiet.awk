# Drops bend's check report from a run's output, so only what the program
# printed is compared against a test's `#|` trailer.
#
# 2.0.16 says "All terms check, with N unsafe annotations." on one line. 2.0.18
# says "All terms check, but N defs rely on unsafe or foreign code:" and then a
# `- <name>` line each. Both go; a test asserting its own output never starts a
# line with "- ".
/^All terms check/ { report = 1; next }
report && /^- /     { next }
                    { report = 0; print }
