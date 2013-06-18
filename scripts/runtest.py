#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, errno, re, glob, shutil, itertools, logging
import subprocess as sp, time, datetime, socket

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
    import ConfigParser as cp
    from optparse import OptionParser

    parser = OptionParser()

    parser.add_option(
        '', '--bin-args',
        action  = 'append',
        metavar = 'ARGS',
        default = [],
        help    = 'append ARGS to EasyCrypt command (cumulative)')

    parser.add_option(
        '', '--xunit',
        action  = 'store',
        default = None,
        metavar = 'FILE',
        help    = 'dump result to FILE using xUnit format')

    (cmdopt, args) = parser.parse_args()

    if len(args) < 1:
        parser.error('this program takes at least one argument')

    options = Object(scenarios = dict())
    options.xunit = cmdopt.xunit

    defaults = dict(args = '', exclude = '', okdirs = '', kodirs = '')

    config = cp.SafeConfigParser(defaults)
    config.read(args[0])

    options.bin     = config.get('default', 'bin')
    options.args    = config.get('default', 'args').split()
    options.targets = args[1:]

    if cmdopt.bin_args:
        options.args.extend(itertools.chain.from_iterable( \
          x.split() for x in cmdopt.bin_args))

    for test in [x for x in config.sections() if x.startswith('test-')]:
        scenario = Object()
        scenario.args    = config.get(test, 'args').split()
        scenario.okdirs  = config.get(test, 'okdirs')
        scenario.kodirs  = config.get(test, 'kodirs')
        scenario.exclude = config.get(test, 'exclude').split()
        options.scenarios[test[5:]] = scenario

    for x in options.targets:
        if x not in options.scenarios:
            parser.error('unknown scenario: %s' % (x,))

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

    timestamp = time.time()
    try:
        command = [options.bin] + options.args + config.args + [config.filename]
        logging.info('command: %r' % (command,))
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
                          args     = obj.args,
                          filename = os.path.normpath(os.path.join(obj.src, x)))

        return [config(x) for x in scripts]

    def gather_for_scenario(scenario):
        def expand(dirs):
            dirs = re.split(r'\s+', dirs)
            dirs = [glob.glob(x) for x in dirs]
            dirs = list(itertools.chain.from_iterable(dirs))
            return dirs

        dirs = []
        dirs.extend([Object(src = x, valid = True , args = scenario.args) \
                         for x in expand(scenario.okdirs)])
        dirs.extend([Object(src = x, valid = False, args = scenario.args) \
                         for x in expand(scenario.kodirs)])
        dirs = [x for x in dirs if x.src not in scenario.exclude]
        dirs = map(lambda x : gather(x), dirs)
        return list(itertools.chain.from_iterable(dirs))

    def gatherall():
        dirs = [options.scenarios[x] for x in options.targets]
        dirs = map(lambda x : gather_for_scenario(x), dirs)
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
