# --------------------------------------------------------------------
import os, subprocess as sp

# --------------------------------------------------------------------
class Resource(object):
    ROOT = os.path.join(os.path.dirname(__file__), 'resources')
    
    @classmethod
    def get(cls, path):
        return os.path.join(cls.ROOT, *path.split('/'))

    @classmethod
    def rcc(cls, name):
        rccname = cls.get('%s.rcc' % (name,))
        qrcname = cls.get('%s.qrc' % (name,))

        if os.path.exists(qrcname):
            try:
                qmtime = os.path.getmtime(qrcname)
                rmtime = os.path.getmtime(rccname)
            except OSError:
                qmtime, rmtime = 1, 0

            if qmtime > rmtime:
                sp.call(['rcc', '-binary', '-o', rccname, qrcname])

        return rccname

    @classmethod
    def ui(cls, name):
        return cls.get('%s.ui' % (name,))

    @classmethod
    def html(cls, name):
        return cls.get('web/templates/%s.html' % (name,))
