# ------------------------------------------------------------------------
import json

from PyQt5 import uic, QtCore #@UnresolvedImport

# ------------------------------------------------------------------------
STOPPED    = 'ec:stopped'
WAITING    = 'ec:waiting'
PROCESSING = 'ec:processing'

# ------------------------------------------------------------------------
class ECState(object):
    def __init__(self):
        self.obuffer  = b''
        self.pllength = -1
        self.uuid     = 0;
        self.state    = STOPPED

# ------------------------------------------------------------------------
class ECProtocolError(Exception):
    def __init__(self, msg = None):
        self.msg = msg

# ------------------------------------------------------------------------
class ECJSon(object):
    def apply(self, driver):
        raise RuntimeError()

# ------------------------------------------------------------------------
class ECJSonNotice(ECJSon):
    def __init__(self, messages):
        self.messages = messages
        
    def apply(self, driver):
        for x in self.messages:
            driver.warning.emit(x)

# ------------------------------------------------------------------------
class ECJSonStep(ECJSon):
    def __init__(self, uuid):
        self.uuid = uuid

    def apply(self, driver):
        driver._state.state = WAITING
        driver.prompt.emit(self.uuid)

# ------------------------------------------------------------------------
class ECJSonProof(ECJSon):
    def __init__(self, proof):
        self.proof = proof

    def apply(self, driver):
        driver.display.emit(self.proof)

# ------------------------------------------------------------------------
class ECJSonError(ECJSon):
    def __init__(self, start, stop, msg):
        self.start = start
        self.stop  = stop
        self.msg   = msg
        
    def apply(self, driver):
        driver.ecerror.emit(self.start, self.stop, self.msg)

# ------------------------------------------------------------------------
def ecjson_of_json(json):
    if not isinstance(json.get('type', None), str):
        raise ECProtocolError('invalid or missing type field')
    
    if json['type'] == 'notice':
        if not isinstance(json.get('value', None), str):
            raise ECProtocolError('invalid `notice` packet')
        return ECJSonNotice([x.strip() for x in json['value'].splitlines()])
    
    if json['type'] == 'step':
        if not isinstance(json.get('step', None), int):
            raise ECProtocolError('invalid `step` packet')
        return ECJSonStep(json['step'])
    
    if json['type'] == 'proof':
        if not isinstance(json.get('value', None), str):
            raise ECProtocolError('invalid `type` package')
        return ECJSonProof(json['value'])
    
    if json['type'] == 'error':
        if    not isinstance(json.get('value', None), str) \
           or not isinstance(json.get('start', None), int) \
           or not isinstance(json.get('stop' , None), int):
            raise ECProtocolError('invalid `error` packet')
        return ECJSonError(json['start'], json['stop'], json['value'])

    raise ECProtocolError('invalid packet type [%s]' % json['type'])

# ------------------------------------------------------------------------
class ECDriver(QtCore.QObject):
    exited  = QtCore.pyqtSignal(bool)
    warning = QtCore.pyqtSignal(str)
    ecerror = QtCore.pyqtSignal(int, int, str)
    display = QtCore.pyqtSignal(str)
    prompt  = QtCore.pyqtSignal(int)

    def __init__(self, binary = 'easycrypt', parent = None, **kw):
        super().__init__(parent)

        cwd, args = kw.get('cwd', None), ['-webui']
        if kw.get('why3', None):
            args.extend(['-why3', kw['why3']])
        
        self._process = QtCore.QProcess(self)
        self._state   = ECState()
        self._process.closeReadChannel(QtCore.QProcess.StandardError)
        self._process.error.connect(self._on_error)
        self._process.finished.connect(self._on_exit)
        self._process.readyReadStandardOutput.connect(self._on_read)
        self._process.setProgram(binary)
        self._process.setArguments(args)
        if cwd: self._process.setWorkingDirectory(cwd)

    state  = QtCore.pyqtProperty(str, lambda self : self._state.state)
    uuid   = QtCore.pyqtProperty(int, lambda self : self._state.uuid)
    foo    = QtCore.pyqtProperty(int, lambda self : QtCore.QThread.currentThreadId())

    def start(self):
        self._state.state = PROCESSING
        self._process.start()

    @QtCore.pyqtSlot('QString')
    def send(self, sentence):
        if self._state.state != WAITING:
            return False
        sentence = sentence.rstrip()
        if not sentence.endswith('.'):
            raise ValueError
        self._state.state = PROCESSING
        self._process.write(sentence.encode('utf-8'))
        self._process.write('\n')
        return True

    @QtCore.pyqtSlot()
    def close(self):
        self._state = ECState()
        self._process.kill()

    def _u(self, msg):
        return msg.decode('utf-8')

    def _on_error(self, err):
        self.close()
        
    def _on_exit(self, code, status):
        self.exited.emit(code == 0)

    def _on_read(self):
        self._state.obuffer += bytes(self._process.readAllStandardOutput())
        while True:
            try:
                if self._state.pllength < 0:
                    if len(self._state.obuffer) >= 8:
                        try:
                            self._state.pllength = int(self._state.obuffer[0:8])
                            self._state.obuffer  = self._state.obuffer[8:]
                        except ValueError:
                            raise ECProtocolError('invalid payload length')
                    else:
                        break
                if len(self._state.obuffer) >= self._state.pllength:
                    data = self._state.obuffer[0:self._state.pllength]
                    self._state.obuffer  = self._state.obuffer[self._state.pllength:]
                    self._state.pllength = -1
                    try:
                        data = json.loads(data.decode('utf-8'))
                        data = ecjson_of_json(data)
                    except Exception:
                        raise ECProtocolError('invalid (json) payload')
                    data.apply(self)

            except ECProtocolError as e:
                print(e.msg)
                self.close()
