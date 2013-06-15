#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, errno, shutil, itertools, logging, subprocess as sp
import time, datetime, socket

# --------------------------------------------------------------------
class Object(object):
    def __init__(self, **kw):
        self.__dict__.update(kw)

# --------------------------------------------------------------------
class ANSIColor(object):
    BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE = range(8)

    @staticmethod
    def _hascolors():
        if not hasattr(sys.stdout, "isatty"):
            return False
        if not sys.stdout.isatty():
            return False

        try:
            import curses

            curses.setupterm()
            return curses.tigetnum("colors") > 2
        except:
            return False

    @staticmethod
    def color(txt, color):
        if ANSIColor.hascolors:
            return "\x1b[1;%dm%s\x1b[0m" % (30+color, txt)
        return txt

ANSIColor.hascolors = ANSIColor._hascolors()

def red  (txt): return ANSIColor.color(txt, ANSIColor.RED  )
def green(txt): return ANSIColor.color(txt, ANSIColor.GREEN)

def rcolor(txt, b):
    return (green if b else red)(txt)

# --------------------------------------------------------------------
def _options():
    from optparse import OptionParser

    def extra_args_callback(option, opt_str, value, parser):
        if len(parser.values.dirs) == 0:
            parser.error('no active scenario for --extra-args')
        parser.values.dirs[-1].extra.append(value)

    def dir_args_callback(option, opt_str, value, parser):
        x = Object(src = value, valid = None, extra = [])

        if opt_str == '--ok-dir': x.valid = True
        if opt_str == '--ko-dir': x.valid = False

        parser.values.dirs.append(x)

    parser = OptionParser()

    parser.add_option(
        '', '--bin',
        help    = 'path to EasyCrypt binary',
        default = 'ec.byte')

    parser.add_option(
        '', '--bin-args',
        action  = 'append',
        metavar = 'ARGS',
        default = [],
        help    = 'append ARGS to EasyCrypt command (cumulative)')

    parser.add_option(
        '', '--extra-args',
        action   = 'callback',
        metavar  = 'ARGS',
        type     = 'string',
        dest     = 'dirs',
        default  = [],
        nargs    = 1,
        callback = extra_args_callback,
        help     = 'append ARGS to EasyCrypt command (cumulative) for last scenarioa')

    parser.add_option(
        '', '--ok-dir',
        action   = 'callback',
        callback = dir_args_callback,
        metavar  = 'DIR',
        type     = 'string',
        dest     = 'dirs',
        nargs    = 1,
        help     = 'path to directory containing *valid* EasyCrypt scripts (cumulative)')

    parser.add_option(
        '', '--ko-dir',
        action   = 'callback',
        callback = dir_args_callback,
        metavar  = 'DIR',
        type     = 'string',
        dest     = 'dirs',
        nargs    = 1,
        help     = 'path to directory containing *invalid* EasyCrypt scripts (cumulative)')

    parser.add_option(
        '', '--xunit',
        action  = 'store',
        default = None,
        metavar = 'FILE',
        help    = 'dump result to FILE using xUnit format')

    (options, args) = parser.parse_args()

    if len(args) != 0:
        parser.error('this program does not take arguments')

    if not options.dirs:
        parser.error('no path to directory containing EasyCrypt scripts given')

    options.bin_args = \
        list(itertools.chain(*[x.split() for x in options.bin_args]))

    for d in options.dirs:
        d.extra = list(itertools.chain(*[x.split() for x in d.extra]))

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
            classname = classname.split(os.path.sep)
            if classname == [] or classname[0] != 'tests':
                classname.insert(0, 'tests')
            classname = '.'.join(classname)

            rnode = E.testcase(
                name      = name,
                classname = classname,
                time      = "%.3f" % (result.time,))
            if not result.success:
                rnode.append(E.failure(result.stderr, \
                        message = \
                            'invalid-exit-status (should-pass: %r)' % \
                                (result.config.isvalid,),
                        type = 'should-pass: %r' % (result.config.isvalid,),))
            node.append(rnode)

        node.append(E("system-out"))
        node.append(E("system-err"))

        root.append(node)

    return lxml.etree.tostring(root,
                               pretty_print    = True   ,
                               xml_declaration = True   ,
                               encoding        = 'utf-8')

# --------------------------------------------------------------------
def _run_test(config, options):
    logging.info("running ec on `%s' [valid: %s]" % \
                     (config.filename, config.isvalid))

    if config.extrargs:
        logging.info("extra arguments: %r" % (config.extrargs,))

    timestamp = time.time()
    try:
        command = [options.bin] + options.bin_args + config.extrargs + [config.filename]
        process = sp.Popen(command, stdout = sp.PIPE, stderr = sp.PIPE)

        try:
            out, err = process.communicate()
            status   = process.poll()
        finally:
            try   : sp.kill()
            except: pass
    except OSError, e:
        logging.error("cannot run `%s': %s" % (options.bin, e))
        exit (1)
    timestamp = time.time() - timestamp
    success   = (bool(status) != bool(config.isvalid))

    logging.info("result for `%s': success: %s" % (config.filename,
                                                   rcolor(success, success)))

    return Object(success = success  ,
                  config  = config   ,
                  time    = timestamp,
                  stderr  = err      )

# --------------------------------------------------------------------
def _main():
    # ------------------------------------------------------------------
    options = _options()

    logging.basicConfig(
        stream = sys.stderr,
        level  = logging.DEBUG,
        format = '%(asctime)-15s - %(levelname)s - %(message)s')

    # ------------------------------------------------------------------
    def gather(obj):
        logging.debug("gathering scripts in `%s'" % (obj.src,))
        try:
            scripts = os.listdir(obj.src)
        except OSError, e:
            logging.warning("cannot scan `%s': %s" % (obj.src, e))
            return []
        scripts = sorted([x for x in scripts if x.endswith('.ec')])
        logging.debug("%.4d script(s) found in `%s'" % (len(scripts), obj.src))

        def config(filename):
            return Object(isvalid  = obj.valid,
                          group    = obj.src,
                          extrargs = obj.extra,
                          filename = os.path.normpath(os.path.join(obj.src, x)))

        return [config(x) for x in scripts]

    def gatherall():
        dirs = map(lambda x : gather(x), options.dirs)
        return list(itertools.chain.from_iterable(dirs))

    allscripts = gatherall()

    logging.debug("%.4d script(s) in total" % (len(allscripts,)))

    # --------------------------------------------------------------------
    mainconfig = Object()
    result = []

    mainconfig.hostname  = socket.gethostname()
    mainconfig.timestamp = datetime.datetime.utcnow()

    for config in allscripts:
        result.append(_run_test(config, options))

    errors = [x for x in result if not x.success]

    logging.info(red("# of failed scripts: %d" % (len(errors,))))
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
