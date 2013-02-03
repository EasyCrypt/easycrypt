#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, errno, shutil, itertools, logging, subprocess as sp
import time, datetime, socket

# --------------------------------------------------------------------
class Object(object):
    def __init__(self, **kw):
        self.__dict__.update(kw)

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

    parser.add_option(
        '', '--xunit',
        action  = 'store',
        default = None,
        metavar = 'FILE',
        help    = 'dump result to FILE using xUnit format')

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
def _xunit_dump(config, results):
    import lxml, lxml.builder; E = lxml.builder.ElementMaker()

    totaltime = sum([x.time for x in results])
    grouped   = dict()

    for result in results:
        grouped.setdefault(result.config.group, []).append(result)

    root = E.testsuites()
    for gname, group in grouped.iteritems():
        ok = [x for x in group if     x.success]
        ko = [x for x in group if not x.success]

        node = E.testsuite(name      = gname,
                           hostname  = config.hostname,
                           timestamp = config.timestamp.isoformat(),
                           tests     = str(len(group)),
                           errors    = "0",
                           failures  = str(len(ko)),
                           time      = "%.3f" % totaltime)

        node.append(E.properties())

        for result in group:
            name = os.path.basename(result.config.filename)
            name = os.path.splitext(name)[0]
            classname = os.path.dirname(result.config.filename)
            classname = '.'.join(classname.split(os.path.sep))

            rnode = E.testcase(
                name      = name,
                classname = classname,
                time      = "%.3f" % (result.time,))
            if not result.success:
                rnode.append(E.failure( \
                        message = \
                            'invalid-exit-status (should-pass: %r)' % \
                                (result.config.isvalid,),
                        type = 'should-pass: %r' % (result.config.isvalid,)))
            node.append(rnode)

        node.append(E("system-out"))
        node.append(E("system-err"))

        root.append(node)

    return lxml.etree.tostring(root,
                               pretty_print    = True   ,
                               xml_declaration = True   ,
                               encoding        = 'utf-8')

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

        def config(filename):
            return Object(isvalid  = isvalid,
                          group    = dirname,
                          filename = os.path.normpath(os.path.join(dirname, x)))

        return [config(x) for x in scripts]

    def gatherall():
        oks = map(lambda x : gather(x, True ), options.ok_dir)
        kos = map(lambda x : gather(x, False), options.ko_dir)
        return list(itertools.chain.from_iterable(oks + kos))

    allscripts = gatherall()

    logging.debug("%.4d script(s) in total" % (len(allscripts,)))

    # --------------------------------------------------------------------
    mainconfig = Object()
    result = []

    mainconfig.hostname  = socket.gethostname()
    mainconfig.timestamp = datetime.datetime.utcnow()

    for config in allscripts:
        logging.info("running ec on `%s' [valid: %s]" % \
                         (config.filename, config.isvalid))
        timestamp1 = time.time()
        try:
            status = sp.call([options.bin, config.filename],
                             stdout = open(os.devnull, 'wb'),
                             stderr = sp.STDOUT)
        except OSError, e:
            logging.error("cannot run `%s': %s" % (options.bin, e))
            exit (1)
        timestamp2 = time.time()
        success = (bool(status) != config.isvalid)
        logging.info("result for `%s': success: %s" % (config.filename, success))
        result.append(Object(success = success,
                             config  = config ,
                             time    = timestamp2 - timestamp1))

    errors = [x for x in result if not x.success]

    logging.info("# of failed scripts: %d" % (len(errors,)))
    if errors:
        logging.info("--- BEGIN FAILING SCRIPTS ---")
        for error in errors:
            logging.info(error.config.filename)
        logging.info("--- END FAILING SCRIPTS ---")
        logging.critical("some tests did NOT pass")

    if options.xunit is not None:
        open(options.xunit, 'wb').write(_xunit_dump(mainconfig, result))

    exit (2 if errors else 0)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
