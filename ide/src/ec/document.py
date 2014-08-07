# ------------------------------------------------------------------------
from PyQt5 import QtCore #@UnresolvedImport

# ------------------------------------------------------------------------
class ECDocument(QtCore.QObject):
    def __init__(self, contents, parent = None):
        assert(isinstance(contents, str))
        super().__init__(parent)
        self.rows = contents.splitlines()

    @QtCore.pyqtSlot(result = int)
    def getLength(self):
        return len(self.rows)
    
    @QtCore.pyqtSlot(int, result = 'QString')
    def getRow(self, index):
        return self.rows[index]

    @QtCore.pyqtSlot(int, int, result = 'QStringList')
    def getRows(self, from_, to_):
        return self.rows[from_:to_]

    @QtCore.pyqtSlot(int, 'QString')
    def setRow(self, index, row):
        self.rows[index] = row

    @QtCore.pyqtSlot(int, 'QString')
    def insertLine(self, index, row):
        self.rows.insert(index, row)

    @QtCore.pyqtSlot(int, 'QStringList')
    def insertLines(self, index, rows):
        self.rows[index:index] = rows
    
    @QtCore.pyqtSlot(int)
    def removeRow(self, index):
        del self.rows[index]
        
    @QtCore.pyqtSlot(int, int)
    def removeRows(self, from_, to_):
        del self.rows[from_:to_]

# ------------------------------------------------------------------------
class ECDocumentManager(QtCore.QObject):
    loaded = QtCore.pyqtSignal()

    def __init__(self, parent = None):
        super().__init__(parent)
        self._document = None

    def getDocument(self):
        return self._document

    def setDocument(self, document):
        assert(isinstance(document, ECDocument))
        self._document = document
        self.loaded.emit()

    document = QtCore.pyqtProperty('QVariant', getDocument, setDocument)
