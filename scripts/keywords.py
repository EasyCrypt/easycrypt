#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, time, itertools as it

# --------------------------------------------------------------------
def _options():
    from optparse import OptionParser

    parser = OptionParser(usage = 'Usage: %prog [options]')

    parser.add_option(
        '-m', '--mode',
        default = 'raw',
        help    = 'output mode (raw|emacs|javascript)')

    (options, args) = parser.parse_args()

    if len(args) != 0:
        parser.error('this program does not take any argument')

    if options.mode not in ('raw', 'emacs', 'javascript'):
        parser.error("invalid mode: `%s'" % (options.mode,))

    return options

# --------------------------------------------------------------------
def process():
    options  = _options()
    keywords = dict()

    for line in sys.stdin:
        line = re.sub(r'\s+', '', line)
        mtch = re.search(r'^"(.*?)",(.*?);\(\*KW:(.*?)\*\)$', line)

        if mtch is not None:
            keywords.setdefault(mtch.group(3), []).append(mtch.group(1))

    if options.mode == 'raw':
        for k in sorted(keywords.keys()):
            print "%s: %s" % (k, ", ".join(sorted(keywords[k])))

    if options.mode == 'emacs':
        print "; Generated on %s" % (time.ctime(),)
        print
        for k in sorted(keywords.keys()):
            print "(defvar easycrypt-%s-keywords '(" % (k,)
            for v in keywords[k]:
                print "  \"%s\"" % (v,)
            print "))"
            print
        print "(provide 'easycrypt-keywords)"

    if options.mode == 'javascript':
        print "// Generated on %s" % (time.ctime(),)
        print 'var cKeywords = "%s"' % \
                (' '.join(sorted(set(it.chain(*keywords.values())))))
        print "// END"

# --------------------------------------------------------------------
if __name__ == '__main__':
    process()
