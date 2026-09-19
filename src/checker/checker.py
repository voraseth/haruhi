#!/usr/bin/env python3
"""Membership checker (Algorithm 1 of the paper).
Counts the distinct permutations of 123456 occurring as 6-character
windows of the input string.  A superpermutation must score 720/720.

Whitespace anywhere in the file is ignored, exactly as verify6.c does, so the
two independently written checkers agree on a line-wrapped witness; any other
character is an error.  Exits 0 iff the string is a superpermutation.

The whitespace class is verify6.c's EXACTLY -- newline, carriage return, space,
tab, and nothing else.  `str.split()` would have been wrong here: it also drops
\f, \v and U+00A0, which verify6.c rejects as bad characters, so the two
checkers would have disagreed on a file containing one of those."""
import re
import sys
raw = open(sys.argv[1]).read()
s = re.sub(r"[\n\r \t]", "", raw)             # verify6.c: `c=='\n'||c=='\r'||c==' '||c=='\t'`
bad = set(s) - set("123456")
if bad:
    sys.exit(f"bad characters {sorted(bad)} in {sys.argv[1]}")
seen = set()
for i in range(len(s) - 5):
    w = s[i:i+6]
    if sorted(w) == ["1", "2", "3", "4", "5", "6"]:
        seen.add(w)
print(f"length={len(s)} distinct_perms={len(seen)} "
      + ("VALID_SUPERPERM6" if len(seen) == 720 else "NOT_A_SUPERPERM"))
sys.exit(0 if len(seen) == 720 else 1)
