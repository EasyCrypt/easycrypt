# ------------------------------------------------------------------------
import os, json

from PyQt5 import QtCore, QtWidgets, QtWebKitWidgets #@UnresolvedImport

from resources import Resource
from document  import ECDocument, ECDocumentManager

# ------------------------------------------------------------------------
class JSObject(object):
    def __init__(self, frame, name):
        self.frame = frame
        self.name  = name

    def __getattr__(self, attr):
        class Proxy(object):
            def __init__(self, frame, objname, funcname):
                self.frame = frame
                self.name  = '%s.%s' % (objname, funcname)

            def __call__(self, *args):
                argstr = ','.join(json.dumps(arg) for arg in args)
                return self.frame.evaluateJavaScript('%s(%s)' % (self.name, argstr))

        return Proxy(self.frame, self.name, attr)

# ------------------------------------------------------------------------
class ECEditor(QtWidgets.QWidget):
    def __init__(self, parent = None):
        super().__init__(parent)

        self._view     = QtWebKitWidgets.QWebView(self)
        self._editor   = None
        self._sopts    = {}
        self._manager  = ECDocumentManager()

        self._view.page().mainFrame().addToJavaScriptWindowObject('ecmanager', self._manager)
        self._view.loadFinished.connect(self._cb_ready)
        self._view.load(QtCore.QUrl.fromLocalFile(Resource.html('editor')))

        self.setLayout(QtWidgets.QHBoxLayout())
        self.layout().setContentsMargins(0, 0, 0, 0)
        self.layout().addWidget(self._view)

    ready    = property(lambda self : self._editor is not None)
    document = property(lambda self : self._document)

    def _cb_ready(self):
        self._editor = JSObject(self._view.page().mainFrame(), 'editor')

    @staticmethod
    def getThemes():
        themes = os.listdir(Resource.get('web/ace/src-noconflict'))
        themes = [x.split('-', 1)[1] for x in themes if x.startswith('theme-')]
        themes = [os.path.splitext(x)[0] for x in themes if x.endswith('.js')]
        themes = [x.replace('_', '-') for x in themes]
        return themes

    def setTheme(self, theme):
        self._editor.setTheme('ace/theme/%s' % (theme,))

    def setContents(self, contents):
        self._manager.setDocument(ECDocument(contents))

    def search(self, needle):
        print(self._sopts)
        self._sopts = self._editor.find(needle, self._sopts, True)

    def resetSearch(self):
        self._sopts = {}
