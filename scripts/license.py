#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 < 1:
        print >>sys.stderr, 'Usage: %s [license] [files...]' % (sys.argv[0],)
        exit(1)

    with open(sys.argv[1], 'r') as stream:
        license_ = stream.readlines()
        license_ = [' * %s' % (x,) for x in license_]
        license_ = ['(* %s' % ('-' * 68,)] + license_ + [' * %s *)' % ('-' * 68,)]
        license_ = '\n'.join([x.rstrip('\r\n') for x in license_]) + '\n\n'

    for filename in sys.argv[2:]:
        with open(filename, 'r') as stream:
            contents = stream.read()
        m = re.search(r'^\s*\(\*[^A-Za-z0-9]*copyright.*?\*\)\s*',
                      contents, re.S | re.I)
        if m is not None:
            contents = contents[m.end():]
        try: os.unlink(filename + '~')
        except OSError: pass
        os.rename(filename, filename + '~')
        with open(filename, 'w') as stream:
            stream.write(license_)
            stream.write(contents)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
