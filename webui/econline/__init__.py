# --------------------------------------------------------------------
import os, subprocess as sp

# --------------------------------------------------------------------
__all__ = ['main']

# --------------------------------------------------------------------
def _routing(config):
    config.add_route('home' , '/')
    config.add_route('tryme', '/tryme')

# --------------------------------------------------------------------
def main(global_config, **settings):
    from pyramid.config import Configurator

    config = Configurator(settings=settings)
    config.include('.renderer.pyramid_genshi')
    config.add_static_view('static', 'static', cache_max_age=3600)
    config.include(_routing)
    config.scan(ignore = 'econline.backend')

    return config.make_wsgi_app()
