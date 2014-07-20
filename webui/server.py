#!/usr/bin/env python

import json

import tornado.escape
import tornado.ioloop
import tornado.process as tproc
import tornado.web
import tornado.websocket

def jsonsplit(s):
    def parseError(desc):
        print "ERROR ({}) parsing:\n======\n{}\n======".format(desc, s)
        exit(-1)

    if s == "":
        return []

    if not s[0].isdigit():
        parseError("not length-prefixed")

    i = 0
    while s[i].isdigit(): i += 1
    objlen = int(s[:i])

    offset = objlen + i
    obj = s[i:offset]
    if obj[0] != '{' or obj[-1] != '}':
        parseError("bad length or malformed JSON object")

    return [obj] + jsonsplit(s[offset:])

class EasyCryptHandler(tornado.websocket.WebSocketHandler):
    ec = None

    # Spawn a new EasyCrypt instance
    def open(self):
        self.ec = tproc.Subprocess(['easycrypt', '-webui'],
                                   stdin=tproc.Subprocess.STREAM,
                                   stdout=tproc.Subprocess.STREAM)
        print "New connection (EasyCrypt instance: {})".format(self.ec.pid)

        # Redirect the output stream to the websocket
        def nop(x): pass
        self.ec.stdout.read_until_close(callback=nop,
                                        streaming_callback=self.send)

    # Process-side callbacks
    def send(self, msg):
        for jsobj in jsonsplit(msg):
            print "Sending:", jsobj
            self.write_message(jsobj)

    # WebSocket-side callbacks
    def on_message(self, msg):
        self.ec.stdin.write(tornado.escape.utf8(msg))

    def on_close(self):
        print "Closed connection (EasyCrypt instance: {})".format(self.ec.pid)
        for s in [self.ec.stdin, self.ec.stdout, self.ec.stderr]:
            s.close()

application = tornado.web.Application([
    (r"/", EasyCryptHandler)
])

if __name__ == "__main__":
    application.listen(8888)
    try:
        tornado.ioloop.IOLoop.instance().start()
    except KeyboardInterrupt:
        print "\nStopped."
