#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, itertools as it, subprocess as sp
import glob, fnmatch

# --------------------------------------------------------------------
MYROOT  = os.path.dirname(__file__)
INSTALL = os.path.join(MYROOT, 'install-sh')

# --------------------------------------------------------------------
def _error(message):
    print >>sys.stderr, "%s: %s" % (sys.argv[0], message)
    exit(1)

# --------------------------------------------------------------------
def _exec(command):
    print >>sys.stderr, ' '.join(command)
    sp.check_call(command)

# --------------------------------------------------------------------
def install_dir(distdir, x):
    fulldir = os.path.join(distdir, x)
    command = [INSTALL, '-m', '0755', '-d', fulldir]

    _exec(command)

# --------------------------------------------------------------------
def install_files(distdir, x, files):
    fulldir  = os.path.join(distdir, x)
    filesR   = [os.path.join(x, f) for (f, b) in files if not b]
    filesX   = [os.path.join(x, f) for (f, b) in files if     b]

    command1 = [INSTALL, '-m', '0755', '-t', fulldir] + filesX
    command2 = [INSTALL, '-m', '0644', '-t', fulldir] + filesR

    if filesX: _exec(command1)
    if filesR: _exec(command2)

# --------------------------------------------------------------------
def _find(dirname, glob):
    for dirpath, dirnames, filenames in os.walk(dirname):
        for filename in fnmatch.filter(filenames, glob):
            yield os.path.join(dirpath, filename)

# --------------------------------------------------------------------
def _expand(x):
    if re.search('^.+:', x) is not None:
        findm = re.search(r'^find:(.*?):(.*$)$', x)
        if findm is not None:
            return list(_find(findm.group(1), findm.group(2)))
        return []

    if not hasattr(glob, 'has_magic') or glob.has_magic(x):
        return glob.glob(x)
    return [x]

# --------------------------------------------------------------------
def _exclude(x):
    exclm = re.search('^exclude:(.+)$', x)
    if exclm is not None:
        exclm = exclm.group(1)
        if not hasattr(glob, 'has_magic') or glob.has_magic(exclm):
            return glob.glob(exclm)
        return [exclm]

    return []

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 != 2:
        print >>sys.stderr, "Usage: %s [dist-dir] [MANIFEST]" % (sys.argv[0])
        exit (1)

    distdir  = sys.argv[1]
    manifest = sys.argv[2]

    contents = open(manifest, 'r').readlines()
    contents = [re.sub('#.*$', '', x).strip() for x in contents]
    contents = [x for x in contents if x]

    exclude  = contents
    exclude  = list(it.chain(*[_exclude(x) for x in exclude]))
    exclude  = set([os.path.normpath(x) for x in exclude])

    manifest = contents
    manifest = list(it.chain(*[_expand(x) for x in manifest]))
    manifest = [os.path.normpath(x) for x in manifest]
    manifest = [x for x in manifest if x not in exclude]

    noaccess = [x for x in manifest if not os.access(x, os.F_OK)]

    if noaccess:
        msg = 'cannot access the following MANIFEST files: %s'
        _error(msg % ', '.join(noaccess))

    bygroup = dict()

    for x in manifest:
        if os.path.isdir(x):
            bygroup.setdefault(x, [])
        else:
            (xdir, xbase) = os.path.split(x)
            xexec = os.access(x, os.X_OK)
            bygroup.setdefault(xdir, []).append((xbase, xexec))

    for x, v in bygroup.iteritems():
        install_dir(distdir, x)
        install_files(distdir, x, v)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
