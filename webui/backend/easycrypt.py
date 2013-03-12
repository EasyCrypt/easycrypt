#! /usr/bin/env python

# --------------------------------------------------------------------l
import sys, os, json, logging
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

    def analyzer(self, message):
        cont = message['end']['contents']
        if cont.find("axim") != -1 :
            error = json.dumps({     'mode' : 'error',
                                     'end'  : message['end'],
                                'start_err' : '2',
                                  'end_err' : '6',
                                  'message' : 'We have an error!' })
            self.websocket.send(error)
        else:
            self.websocket.send(json.dumps(message))

    def run(self):
        while True:
            message = self.websocket.receive()
            if message is None:
                return
            message = json.loads(message)

            if  message['mode'] == 'undo' :
                undo = json.dumps({'mode' : 'undo', 'data' : 'Undo operation - OK'})
                self.websocket.send(undo)
            elif message['mode'] == 'forward' :
                self.analyzer(message)

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
