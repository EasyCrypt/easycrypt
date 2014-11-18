# ------------------------------------------------------------------------
import json

from PyQt5 import QtCore, QtWidgets, QtWebKitWidgets #@UnresolvedImport

from ec.resources import Resource
from ec.driver    import ECDriver

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
# FIXME: emit a signal when the driver is changed
class ECObjManager(QtCore.QObject):
    def __init__(self, parent = None):
        super().__init__(parent)
        self._driver   = None

    def getDriver(self):
        return self._driver

    def setDriver(self, driver):
        assert(isinstance(driver, ECDriver))
        if self._driver and self._driver.parent() is self:
            self._driver.deleteLater()
        self._driver = driver

    driver = QtCore.pyqtProperty('QVariant', getDriver  , setDriver)

# ------------------------------------------------------------------------
class ECEditor(QtWidgets.QWidget):
    def __init__(self, parent = None):
        super().__init__(parent)

        self._view     = QtWebKitWidgets.QWebView(self)
        self._editor   = None
        self._sopts    = {}
        self._manager  = ECObjManager(self)
        self._driver   = None

        self._view.page().mainFrame().addToJavaScriptWindowObject('ecmanager', self._manager)
        self._view.loadFinished.connect(self._cb_ready)
        self._view.load(QtCore.QUrl.fromLocalFile(Resource.html('editor')))

        self.setLayout(QtWidgets.QHBoxLayout())
        self.layout().setContentsMargins(0, 0, 0, 0)
        self.layout().addWidget(self._view)

    ready    = property(lambda self : self._editor is not None)
    document = property(lambda self : self._document)
    driver   = property(lambda self : self._driver)

    def _cb_ready(self):
        self._editor = JSObject(self._view.page().mainFrame(), 'editor')

    def to_cursor(self):
        return self._editor.to_cursor()

    def next_sentence(self):
        return self._editor.next_sentence()
        
    def prev_sentence(self):
        return self._editor.prev_sentence()

    def set_contents(self, contents=''):
        self._editor.set_contents(contents)

    def set_driver(self, driver):
        self._manager.setDriver(driver)

    def search(self, needle):
        self._sopts = self._editor.find(needle, self._sopts, True)

    def reset_search(self):
        self._sopts = {}
