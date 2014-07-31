# ------------------------------------------------------------------------
from PyQt5 import QtCore #@UnresolvedImport

# ------------------------------------------------------------------------
class ECDocument(QtCore.QObject):
    loaded = QtCore.pyqtSignal()

    def __init__(self, parent):
        super().__init__(parent)
        self._contents = ''    

    def getContents(self):
        return self._contents

    def setContents(self, contents):
        self._contents = contents
        self.loaded.emit()

    contents = QtCore.pyqtProperty('QString', getContents, setContents)
