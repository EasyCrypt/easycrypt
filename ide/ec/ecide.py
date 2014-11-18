# --------------------------------------------------------------------
import sys, os, html
import ec.resources as resources, ec.driver as driver

from PyQt5 import uic, QtCore, QtGui, QtWidgets, QtWebKit #@UnresolvedImport

# cx_freeze fails to find this dependency
from PyQt5 import QtPrintSupport #@UnresolvedImport @UnusedImport

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
        self._ui.search.textChanged.connect(self._ui.editor.search)

        self._ui.menu.addAction(baction)
        self._ui.menu.addSeparator()
        self._ui.menu.addAction(self._ui.action_ec_previous)
        self._ui.menu.addAction(self._ui.action_ec_to_cursor)
        self._ui.menu.addAction(self._ui.action_ec_next)
        self._ui.menu.addWidget(QTUtils.HWSpacer(1, self))
        self._ui.menu.addWidget(self._ui.search)
        bmenu.setAutoRaise(False)

        self._process = driver.ECDriver(parent=self)
        self._process.warning.connect(self._on_ec_warning)
        self._process.exited.connect(self._on_ec_exited)
        self._process.ecerror.connect(self._on_ec_error)
        self._process.display.connect(self._on_ec_display)
        self._process.start()
        
        self._ui.editor.set_driver(self._process)

    def _on_ec_exited(self, ok):
        self._ui.messages.appendHtml('<b>%s</b>\n' % 'EasyCrypt process exited')

    def _on_ec_display(self, display):
        self._ui.proofenv.setPlainText(display)

    def _on_ec_warning(self, msg):
        self._ui.messages.appendHtml('<i>%s</i>\n' % html.escape(msg.rstrip('\r\n')))

    def _on_ec_error(self, start, stop, msg):
        self._ui.messages.appendHtml('<b>%s</b>\n' % html.escape(msg.rstrip('\r\n')))

    @QtCore.pyqtSlot(name='on_action_open_triggered')
    def _ui_open(self):
        filename = QtWidgets.QFileDialog.getOpenFileName(self)[0]
        if not filename: return
        with open(filename, 'rb') as stream:
            contents = stream.read()
        #mg = magic.open(magic.MAGIC_MIME_ENCODING); mg.load()
        #encoding = mg.buffer(contents)
        contents = str(contents, 'utf-8')
        self._ui.editor.set_contents(contents)

    @QtCore.pyqtSlot(name='on_action_ec_next_triggered')
    def _ui_ec_next(self):
        if self._process.state == driver.WAITING:
            self._ui.messages.clear()
        self._ui.editor.next_sentence()

    @QtCore.pyqtSlot(name='on_action_ec_to_cursor_triggered')
    def _ui_ec_to_cursor(self):
        if self._process.state == driver.WAITING:
            self._ui.messages.clear()
        self._ui.editor.to_cursor();
    
    @QtCore.pyqtSlot(name='on_action_ec_previous_triggered')
    def _ui_ec_prev(self):
        if self._process.state == driver.WAITING:
            self._ui.messages.clear()
        self._ui.editor.prev_sentence()

    @QtCore.pyqtSlot(name='on_action_find_triggered')
    def _ui_find(self):
        self._ui.search.setFocus()
        self._ui.search.selectAll()

    @QtCore.pyqtSlot(name='on_action_quit_triggered')
    def _ui_quit(self):
        self.close()

# --------------------------------------------------------------------
def main(forbuild = False):
    app = QtWidgets.QApplication(sys.argv)
    res = resources.Resource.rcc('icons')

    sys.path.append(resources.Resource.ROOT)
    __import__(os.path.splitext(os.path.basename(res))[0])

    if forbuild: return

    QtGui.QIcon.setThemeName("FlatIcon")

    QtWebKit.QWebSettings.globalSettings().setAttribute(
        QtWebKit.QWebSettings.DeveloperExtrasEnabled, True)

    win = MainWindow()
    win.show(); sys.exit(app.exec_())
