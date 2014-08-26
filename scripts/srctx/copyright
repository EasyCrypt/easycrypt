#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re

# --------------------------------------------------------------------
class BoxProcessor(object):
    def get_head_comment(self, contents):
        raise RuntimeError()

    def box(self, contents):
        raise RuntimeError()

# --------------------------------------------------------------------
class MLBoxProcessor(object):
    def __init__(self):
        pass

    def get_head_comment(self, contents):
        m = re.search(r'^\s*\(\*(.*?)\*\)\s*', contents, re.S)
        if m is None:
            return '', contents
        return m.group(1), contents[m.end(0):]

    def box(self, contents):
        contents = contents.splitlines()
        if contents:
            contents[0] = '(* %s' % contents[0]
            for i in xrange(1, len(contents)):
                contents[1] = ' * %s' % contents[i]
            contents[-1] = '%s *)' % contents[-1]
        return '\n'.join(contents) + '\n'

# --------------------------------------------------------------------
class Box(object):
    def __init__(self, copyrg, box):
        self.copyrg = copyrg
        self.box    = box

    def process(self, contents):
        head, tail = self.box.get_head_comment(contents)
        head = re.sub(r'\s+', ' ', head.strip(), re.S)
        if re.search(r'^copyright \(c\)', head, re.I):
           contents = tail
        return '%s\n\n%s' % (self.box.box(self.copyrg).rstrip(), contents)

# --------------------------------------------------------------------
PROCESSORS = {
    '.ml'  : MLBoxProcessor,
    '.mli' : MLBoxProcessor,
    '.mll' : MLBoxProcessor,
    '.mly' : MLBoxProcessor,
}

# --------------------------------------------------------------------
def process1(copyrg, filename):
    ext = os.path.splitext(filename)[1]
    if ext not in PROCESSORS:
        raise RuntimeError('unknown extension: %s' % (ext,))
    with open(filename, 'r') as stream:
        contents = stream.read()
    contents = Box(copyrg, PROCESSORS[ext]()).process(contents)
    with open(filename, 'w') as stream:
        stream.write(contents)


# --------------------------------------------------------------------
def process_all(copyrg, filenames):
    for filename in filenames:
        process1(copyrg, filename)

# --------------------------------------------------------------------
def _main():
    copyrg = os.path.join(os.path.dirname(__file__), '..', 'COPYRIGHT')
    with open(copyrg, 'r') as stream:
        copyrg = stream.read()
    process_all(copyrg, sys.argv[1:])

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
