# --------------------------------------------------------------------
import sys, os

# --------------------------------------------------------------------
class Resource(object):
    ROOT = os.path.join(os.path.dirname(__file__), 'data')

    @classmethod
    def get(cls, path):
        return os.path.join(cls.ROOT, *path.split('/'))

    @classmethod
    def rcc(cls, name, compile=True):
        rccname = cls.get('%srcc.py' % (name,))
        qrcname = cls.get('%s.qrc' % (name,))

        if compile and not getattr(sys, 'frozen', False):
            import subprocess as sp

            if os.path.exists(qrcname):
                try:
                    qmtime = os.path.getmtime(qrcname)
                    rmtime = os.path.getmtime(rccname)
                except OSError:
                    qmtime, rmtime = 1, 0

                if qmtime > rmtime:
                    sp.call(['pyrcc5', '-o', rccname, qrcname])

        return rccname

    @classmethod
    def ui(cls, name):
        return cls.get('%s.ui' % (name,))

    @classmethod
    def html(cls, name):
        return cls.get('web/templates/%s.html' % (name,))

# --------------------------------------------------------------------
if getattr(sys, 'frozen', False):
    Resource.ROOT = os.path.join(os.path.dirname(sys.executable), 'data')
