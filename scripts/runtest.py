#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, errno, shutil, itertools, logging, subprocess as sp

# --------------------------------------------------------------------
def _options():
    from optparse import OptionParser

    parser = OptionParser()

    parser.add_option(
        '', '--bin',
        help    = 'path to EasyCrypt binary',
        default = 'ec.byte')

    parser.add_option(
        '', '--ok-dir',
        action  = 'append',
        metavar = 'LOG',
        default = [],
        help    = 'path to directory containing *valid* EasyCrypt scripts (cumulative)')

    parser.add_option(
        '', '--ko-dir',
        action  = 'append',
        metavar = 'DIR',
        default = [],
        help    = 'path to directory containing *invalid* EasyCrypt scripts (cumulative)')

#    parser.add_option(
#        '', '--log',
#        help    = 'path to directory containing tests logs (must NOT exist)',
#        default = '_log')

    (options, args) = parser.parse_args()

    if len(args) != 0:
        parser.error('this program does not take arguments')

    if not options.ko_dir and not options.ok_dir:
        parser.error('no path to directory containing EasyCrypt scripts given')

    return options

# --------------------------------------------------------------------
def _main():
    # ------------------------------------------------------------------
    options = _options()

    logging.basicConfig(
        stream = sys.stderr,
        level  = logging.DEBUG,
        format = '%(asctime)-15s - %(levelname)s - %(message)s')

    # ------------------------------------------------------------------
#    try:
#        os.mkdir(options.log)
#    except OSError, e:
#        if e.errno == errno.EEXIST:
#            logging.fatal("log directory `%s' exists" % (options.log,))
#        else:
#            logging.fatal("cannot create log directory: %s" % (e,))
#        exit (1)

    # ------------------------------------------------------------------
    def gather(dirname, isvalid):
        logging.debug("gathering scripts in `%s'" % (dirname,))
        try:
            scripts = os.listdir(dirname)
        except OSError, e:
            logging.warning("cannot scan `%s': %s" % (dirname, e))
        scripts = sorted([x for x in scripts if x.endswith('.ec')])
        logging.debug("%.4d script(s) found in `%s'" % (len(scripts), dirname))
        return [(isvalid, os.path.join(dirname, x)) for x in scripts]

    def gatherall():
        oks = map(lambda x : gather(x, True ), options.ok_dir)
        kos = map(lambda x : gather(x, False), options.ko_dir)
        return list(itertools.chain.from_iterable(oks + kos))

    allscripts = gatherall()

    logging.debug("%.4d script(s) in total" % (len(allscripts,)))

    # --------------------------------------------------------------------
    errors = []

    for isvalid, filename in allscripts:
        logging.info("running ec on `%s' [valid: %s]" % (filename, isvalid))
        try:
            status = sp.call([options.bin, filename],
                             stdout = open(os.devnull, 'wb'),
                             stderr = sp.STDOUT)
        except OSError, e:
            logging.error("cannot run `%s': %s" % (options.bin, e))
            exit (1)
        success = (bool(status) != isvalid)
        logging.info("result for `%s': success: %s" % (filename, success))
        if not success:
            errors.append(filename)

    logging.info("# of failed scripts: %d" % (len(errors,)))
    if errors:
        logging.critical("some tests did NOT pass")

    exit (2 if errors else 0)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
