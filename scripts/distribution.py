#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, glob, itertools as it, subprocess as sp

# --------------------------------------------------------------------
def _exec(command):
    print >>sys.stderr, ' '.join(command)
    sp.check_call(command)

# --------------------------------------------------------------------
def install_dir(distdir, x):
    fulldir = os.path.join(distdir, x)
    command = ['install', '-m', '0755', '-d', fulldir]

    _exec(command)

# --------------------------------------------------------------------
def install_files(distdir, x, files):
    fulldir  = os.path.join(distdir, x)
    files    = [os.path.join(x, file) for file in files]
    exe      = [x for x in files if os.access(x, os.X_OK)]
    files    = [x for x in files if x not in exe]

    command1 = ['install', '-m', '0755', '-t', fulldir] + exe
    command2 = ['install', '-m', '0644', '-t', fulldir] + files

    if exe:   _exec(command1)
    if files: _exec(command2)

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 != 2:
        print >>sys.stderr, "Usage: %s [dist-dir] [MANIFEST]" % (sys.argv[0])
        exit (1)

    distdir  = sys.argv[1]
    manifest = sys.argv[2]

    manifest = open(manifest, 'r').readlines()
    manifest = [re.sub('#.*$', '', x).strip() for x in manifest]
    manifest = [x for x in manifest if x]
    manifest = list(it.chain(*[glob.glob(x) for x in manifest]))
    manifest = [os.path.normpath(x) for x in manifest]

    bygroup = dict()

    for x in manifest:
        (xdir, xbase) = os.path.split(x)
        bygroup.setdefault(xdir, []).append(xbase)

    for x, v in bygroup.iteritems():
        install_dir(distdir, x)
        install_files(distdir, x, v)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
