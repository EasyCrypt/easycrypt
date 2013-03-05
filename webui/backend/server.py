#! /usr/bin/env python

import os
from gevent.pywsgi import WSGIServer
import geventwebsocket

class eServer(object):

    def __init__(self):
        path = os.path.dirname(geventwebsocket.__file__)
        agent = "gevent-websocket/%s" % (geventwebsocket.__version__)
        print "Running %s from %s" % (agent, path)
        self.all_socks = []
        self.s = WSGIServer(("", 8000), self.echo, handler_class=geventwebsocket.WebSocketHandler)
        self.broken_socks = []
        self.s.serve_forever()

    def echo(self, environ, start_response):
        websocket = environ.get("wsgi.websocket")
        if websocket is None:
            return http_handler(environ, start_response)
        try:
            while True:
                message = websocket.receive()
                if message is None:
                    break
                self.sock_track(websocket)
                for s in self.all_socks:
                    try:
                        s.send(message)
                    except Exception:
                        print "broken sock"
                        self.broken_socks.append(s)
                        continue
                if self.broken_socks:
                     for s in self.broken_socks:
                         print 'try close socket'
                         s.close()
                         if s in self.all_socks:
                             print 'try remove socket'
                             self.all_socks.remove(s)
                     self.broken_sock = []
                     print self.broken_sock
            websocket.close()
        except geventwebsocket.WebSocketError, ex:
            print "%s: %s" % (ex.__class__.__name__, ex)


    def http_handler(self, environ, start_response):
        if environ["PATH_INFO"].strip("/") == "version":
            start_response("200 OK", [])
            return [agent]
        else:
            start_response("400 Bad Request", [])
            return ["WebSocket connection is expected here."]

    def sock_track(self, s):
        if s not in self.all_socks:
            self.all_socks.append(s)
            print self.all_socks

s = eServer()
