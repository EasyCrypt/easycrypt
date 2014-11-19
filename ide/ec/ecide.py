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

        baction = QtWidgets.QWidgetAction(self)
        bmenu   = QtWidgets.QToolButton(self)
        mmenu   = QtWidgets.QMenu(self)

        bmenu.setMenu(mmenu)
        bmenu.setPopupMode(QtWidgets.QToolButton.InstantPopup)
        bmenu.setIcon(QtGui.QIcon.fromTheme('menu'))
        bmenu.setStyleSheet('QToolButton::menu-indicator { image: none; }')
        baction.setDefaultWidget(bmenu)

        #self._ui.search = QtWidgets.QLineEdit(self)
        #self._ui.search.setPlaceholderText(self.tr('Search'))
        #self._ui.search.setFixedWidth(300)
        #self._ui.search.textChanged.connect(self._ui.editor.search)

        mmenu.addAction(self._ui.action_open)
        mmenu.addSeparator()
        #mmenu.addAction(self._ui.action_find)
        #mmenu.addSeparator()
        mmenu.addAction(self._ui.action_quit)

        self._ui.menu.addAction(baction)
        self._ui.menu.addSeparator()
        self._ui.menu.addAction(self._ui.action_ec_previous)
        self._ui.menu.addAction(self._ui.action_ec_to_cursor)
        self._ui.menu.addAction(self._ui.action_ec_next)
        #self._ui.menu.addWidget(QTUtils.HWSpacer(1, self))
        #self._ui.menu.addWidget(self._ui.search)
        bmenu.setAutoRaise(False)

        ecoptions = dict(
            cwd    = None,
            binary = resources.Resource.easycrypt,
            why3   = None,
        )

        if resources.Resource.frozen:
            ecoptions['cwd']  = resources.Resource.ROOT
            ecoptions['why3'] = 'why3.conf'

        self._process = driver.ECDriver(parent=self, **ecoptions)
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
        # FIXME: parenting problem with QWidgetAction
        self._exit()

    def event(self, event):
        if isinstance(event, QtGui.QCloseEvent):
            self._exit()
        return super().event(event)

    def _exit(self):
            try: self._driver.close()
            except: pass
            sys.exit(0)

# --------------------------------------------------------------------
def _set_state_for_frozen():
    def extend_env(name, value):
        os.environ[name] = '%s%s%s' % (value, os.pathsep, os.environ.get(name, ''))
    root = resources.Resource.ROOT
    extend_env('PATH'             , os.path.join(root, 'bin'))
    extend_env('LD_LIBRARY_PATH'  , os.path.join(root, 'lib'))
    extend_env('DYLD_LIBRARY_PATH', os.path.join(root, 'lib'))

# --------------------------------------------------------------------
def main(forbuild = False):
    if resources.Resource.frozen:
        _set_state_for_frozen()
    
    app = QtWidgets.QApplication(sys.argv)
    res = resources.Resource.rcc('icons')

    sys.path.append(resources.Resource.ROOT)
    sys.path.append(os.path.join(resources.Resource.ROOT, 'data'))
    __import__(os.path.splitext(os.path.basename(res))[0])

    if forbuild: return

    QtGui.QIcon.setThemeName("FlatIcon")

    QtWebKit.QWebSettings.globalSettings().setAttribute(
        QtWebKit.QWebSettings.DeveloperExtrasEnabled, True)

    win = MainWindow()
    win.show(); sys.exit(app.exec_())
