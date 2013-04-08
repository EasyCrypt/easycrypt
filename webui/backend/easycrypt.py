#! /usr/bin/env python

# --------------------------------------------------------------------l
import sys, os, re, json, logging, gevent.subprocess as sp
import cStringIO as sio
import gevent, gevent.monkey, gevent.pywsgi as gwsgi

from geventwebsocket.handler import WebSocketHandler

gevent.monkey.patch_all()

# --------------------------------------------------------------------
logging.basicConfig()
logger = logging.getLogger(__file__)

# --------------------------------------------------------------------
from pyramid.view import view_config
#from pyramid.response import Response

# --------------------------------------------------------------------
class EasyCryptClient(object):
    def __init__(self, websocket):
        self.websocket = websocket
        self.easycrypt = None
        self.prompt    = None

    def __read_prompt(self):
        prompt = sio.StringIO()

        while True:
            content = self.easycrypt.stdout.readline().rstrip('\r\n')
            match   = re.search(r'^\[(\d+)\]>$', content)

            if match is None:
                prompt.write('%s\r\n' % (content,))
            else:
                self.prompt = int(match.group(1))
                return prompt.getvalue()

    def __undo(self, id):
        self.easycrypt.stdin.write('undo %d.\r\n' % (id,))
        self.easycrypt.stdin.flush()

        prompt  = self.__read_prompt()
        message = dict(
            pundo = self.prompt
        )

        self.websocket.send(json.dumps(message))

    def __send(self, statement):
        self.easycrypt.stdin.write(re.sub(r'\r?\n', ' ', statement) + '\r\n')
        self.easycrypt.stdin.flush()

    def __forward(self, contents):
        self.__send(contents)

        pundo  = self.prompt
        prompt = self.__read_prompt()
        match  = re.search('^\[error-\d+-\d+\](.*)', prompt, re.M | re.S)

        if match is None:
            message = dict(
                status  = 'ok'  ,
                message = prompt,
                pundo   = pundo ,
            )
        else:
            assert (pundo == self.prompt)
            message = dict(
                status    = 'error',
                message   = match.group(1),
                start_err = -1,
                end_err   = -1,
            )

        self.websocket.send(json.dumps(message))

    def __run(self):
        while True:
            message = self.websocket.receive()
            if message is None:
                return
            message = json.loads(message)

            if  message['mode'] == 'undo':
                self.__undo(int(message['data']))
            elif message['mode'] == 'forward':
                self.__forward(message['contents'])

    def run(self):
        assert (self.easycrypt == None)

        self.easycrypt = \
            sp.Popen(['../../ec.native', '-emacs'],
                     stdin  = sp.PIPE,
                     stdout = sp.PIPE,
                     stderr = sp.STDOUT)

        try:
            self.__read_prompt()
            self.__run()
        finally:
            try:
                self.easycrypt.kill()
                self.easycrypt.wait()
            except OSError:
                pass
            self.easycrypt = None
            self.prompt    = None

# --------------------------------------------------------------------
@view_config(route_name = 'root', renderer = 'json')
def root(request):
    return {}

# --------------------------------------------------------------------
@view_config(route_name = 'easycrypt', renderer = 'string')
def easycrypt(request):
    websocket = request.environ['wsgi.websocket']
    EasyCryptClient(websocket).run()
    return 'OK'

# --------------------------------------------------------------------
def _routing(config):
    config.add_route('root', '/')
    config.add_route('easycrypt', '/engine')

# --------------------------------------------------------------------
def _main():
    from pyramid.config  import Configurator
    from pyramid.session import UnencryptedCookieSessionFactoryConfig

    from wsgiref.simple_server import make_server

    settings = {}
    settings['reload_all'] = True
    settings['debug_all' ] = True

    session_factory = UnencryptedCookieSessionFactoryConfig('itsaseekreet')
    config = Configurator(settings=settings, session_factory=session_factory)
    _routing(config); config.scan()

    application = config.make_wsgi_app()

    server = gwsgi.WSGIServer(('0.0.0.0', 8080), application,
                              handler_class=WebSocketHandler)
    server.serve_forever()

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
