#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, os, resources, widgets.editor as editor

from PyQt5 import uic, QtCore, QtGui, QtWidgets, QtWebKit #@UnresolvedImport

# --------------------------------------------------------------------
class QTUtils(object):
    @staticmethod
    def HWSpacer(stretch = 1, parent = None):
        aout   = QtWidgets.QWidget(parent)
        policy = QtWidgets.QSizePolicy(
                    QtWidgets.QSizePolicy.Expanding,
                    QtWidgets.QSizePolicy.Preferred)
        policy.setHorizontalStretch(stretch)
        aout.setSizePolicy(policy)
        return aout

    @staticmethod
    def setHorizontalStretch(widget, value):
        policy = widget.sizePolicy()
        policy.setHorizontalStretch(value)
        widget.setSizePolicy(policy)

# --------------------------------------------------------------------
class MainWindow(QtWidgets.QMainWindow):
    def __init__(self, parent = None):
        super().__init__(parent)
        self._ui = uic.loadUiType(resources.Resource.ui('main'))[0]()
        self._ui.setupUi(self)
        self._view = editor.ECEditor(parent = self)

        mmenu = QtWidgets.QMenu(self)
        mmenu.addAction(self._ui.action_open)
        mmenu.addSeparator()
        mmenu.addAction(self._ui.action_find)
        mmenu.addSeparator()
        mmenu.addAction(self._ui.action_quit)

        baction = QtWidgets.QWidgetAction(self)
        bmenu   = QtWidgets.QToolButton(self._ui.menu)

        bmenu.setMenu(mmenu)
        bmenu.setPopupMode(QtWidgets.QToolButton.InstantPopup)
        bmenu.setIcon(QtGui.QIcon.fromTheme('menu'))
        bmenu.setStyleSheet('QToolButton::menu-indicator { image: none; }')
        baction.setDefaultWidget(bmenu)

        self._ui.search = QtWidgets.QLineEdit(self)
        self._ui.search.setPlaceholderText(self.tr('Search'))
        self._ui.search.setFixedWidth(300)
        self._ui.search.textChanged.connect(self._view.search)

        self._ui.menu.addAction(baction)
        self._ui.menu.addSeparator()
        self._ui.menu.addAction(self._ui.action_ec_previous)
        self._ui.menu.addAction(self._ui.action_ec_next)
        self._ui.menu.addWidget(QTUtils.HWSpacer(1, self))
        self._ui.menu.addWidget(self._ui.search)
        bmenu.setAutoRaise(False)

        self.setCentralWidget(self._view)

    @QtCore.pyqtSlot(name='on_action_open_triggered')
    def _ui_open(self):
        filename = QtWidgets.QFileDialog.getOpenFileName(self)[0]
        if not filename: return
        with open(filename, 'rb') as stream:
            contents = stream.read()
        #mg = magic.open(magic.MAGIC_MIME_ENCODING); mg.load()
        #encoding = mg.buffer(contents)
        contents = str(contents, 'utf-8')
        self._view.setContents(contents)

    @QtCore.pyqtSlot(name='on_action_find_triggered')
    def _ui_find(self):
        self._ui.search.setFocus()
        self._ui.search.selectAll()

    @QtCore.pyqtSlot(name='on_action_quit_triggered')
    def _ui_quit(self):
        self.close()

# --------------------------------------------------------------------
def main():
    app = QtWidgets.QApplication(sys.argv)
    res = resources.Resource.rcc('icons')
    
    sys.path.append(resources.Resource.ROOT)
    __import__(os.path.splitext(os.path.basename(res))[0])

    QtGui.QIcon.setThemeName("FlatIcon")

    QtWebKit.QWebSettings.globalSettings().setAttribute(
        QtWebKit.QWebSettings.DeveloperExtrasEnabled, True)

    win = MainWindow()
    win.show(); exit (app.exec_())

# --------------------------------------------------------------------
if __name__ == '__main__':
    main()
