#! /usr/bin/env python

# --------------------------------------------------------------------l
import os, logging

# --------------------------------------------------------------------
logging.basicConfig()
logger = logging.getLogger(__file__)

# --------------------------------------------------------------------
from pyramid.view import view_config

# --------------------------------------------------------------------
@view_config(route_name = 'root', renderer = 'json')
def root(request):
    return dict(backend = 'easycrypt')

# --------------------------------------------------------------------
def _routing(config):
    config.add_route('root', '/')

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
    _routing(config)
    config.scan()

    application = config.make_wsgi_app()
    server = make_server('0.0.0.0', 8080, application)
    server.serve_forever()

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
