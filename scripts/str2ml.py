#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, base64

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 != 1:
        print >>sys.stderr, 'Usage: %s [filename]' % (sys.argv[0],)
        exit(1)

    with open(sys.argv[1], 'r') as stream:
        contents = [x.strip() for x in stream.readlines()]
        contents = [x for x in contents if x]

    print 'let value = ['
    for x in contents:
        print '  "%s";' % (base64.b64encode(x),)
    print ']'

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
