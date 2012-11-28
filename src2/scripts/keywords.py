#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re

# --------------------------------------------------------------------
def process(stream):
    keywords = dict()

    for line in stream:
        line = re.sub(r'\s+', '', line)
        mtch = re.search(r'^"(.*?)",(.*?);\(\*KW:(.*?)\*\)$', line)

        if mtch is not None:
            keywords.setdefault(mtch.group(3), []).append(mtch.group(1))

    for k in sorted(keywords.keys()):
        print "%s: %s" % (k, ", ".join(sorted(keywords[k])))

# --------------------------------------------------------------------
if __name__ == '__main__':
    process(sys.stdin)
