# --------------------------------------------------------------------
# https://code.google.com/p/bag/source/browse/bag/web/pyramid/genshi.py

# --------------------------------------------------------------------
import os

from zope.interface          import implementer
from paste.deploy.converters import asbool
from pyramid.interfaces      import ITemplateRenderer
from pyramid.resource        import abspath_from_resource_spec

import genshi
import genshi.template as gtemplate, genshi.filters as gfilters

# --------------------------------------------------------------------
__all__ = ['load_template', 'GenshiTemplateRenderer', 'includeme']

# --------------------------------------------------------------------
def load_template(asset):
    '''Make the Genshi TemplateLoader work with typical Pyramid asset
    specifications by passing this function to the TemplateLoader
    constructor as one of the paths.
    '''
    abspath  = abspath_from_resource_spec(asset)
    stream   = open(abspath, 'r') # Genshi catches the possible IOError.
    mtime    = os.path.getmtime(abspath)
    filename = os.path.basename(abspath)

    def file_not_changed():
        return mtime == os.path.getmtime(abspath)

    return (abspath, filename, stream, file_not_changed)

# --------------------------------------------------------------------
@implementer(ITemplateRenderer)
class GenshiTemplateRenderer(object):
    def __init__(self, settings):
        dirs  = settings.get('genshi.directories', [])
        if isinstance(dirs, basestring): dirs = [dirs]
        paths = [abspath_from_resource_spec(p) for p in dirs]
        paths.insert(0, load_template)  # enable Pyramid asset specifications

        # http://genshi.edgewall.org/wiki/Documentation/i18n If
        # genshi.translation_domain has a value, we set up a callback
        # in the loader.
        domain = settings.get('genshi.translation_domain')
        if domain:
            from pyramid.i18n        import get_localizer
            from pyramid.threadlocal import get_current_request

            def translate(text):
                return get_localizer(get_current_request()) \
                       .translate(text, domain=domain)

            def callback(template):
                gfilters.Translator(translate).setup(template)
        else:
            callback = None

        self.loader = gtemplate.TemplateLoader(paths, callback=callback,
            auto_reload=asbool(settings.get('pyramid.reload_templates')),
            max_cache_size=int(settings.get('genshi.max_cache_size', 100)))
        self.strip_whitespace = settings.get('genshi.strip_whitespace', True)
        self.doctype = settings.get('genshi.doctype', 'html5')
        self.method  = settings.get('genshi.method', 'xhtml')

    def implementation(self):
        return self

    def __call__(self, value, system):
        """ ``value`` is the result of the view.  Returns a result (a
        string or unicode object useful as a response body). Values
        computed by the system are passed by the system in the
        ``system`` parameter, which is a dictionary. Keys in the
        dictionary include: ``view`` (the view callable that returned
        the value), ``renderer_name`` (the template name or simple
        name of the renderer), ``context`` (the context object passed
        to the view), and ``request`` (the request object passed to
        the view).
        """
        rn = system.get('renderer_name') or system['renderer_info'].name
        template = self.loader.load(rn)

        # Mix the *system* and *value* dictionaries
        system['url']    = system['request'].route_path
        system['chrome'] = system['request'].static_path
        try:
            system.update(value)
        except (TypeError, ValueError):
            raise ValueError(
                'GenshiTemplateRenderer was passed a non-dictionary as value.')

        # Render the template and return a string
        return template.generate(**system) \
            .render(method=self.method,
                    encoding=None,  # so Genshi outputs a unicode object
                    doctype=self.doctype,
                    strip_whitespace=self.strip_whitespace)

    def fragment(self, template, dic):
        """Loads a Genshi template and returns its output as a unicode object
        containing an HTML fragment, taking care of some details.

        * template is the Genshi template file to be rendered.
        * dic is a dictionary to populate the template instance.
        """
        t = self.loader.load(template)
        return t.generate(**dic).render(method=self.method, encoding='utf-8')

# --------------------------------------------------------------------
def includeme(config):
    '''Easily integrates Genshi template rendering into Pyramid.'''
    if hasattr(config, 'bag_genshi_included'):
        return  # Include only once per config
    config.bag_genshi_included = True

    settings = config.get_settings()
    # By default, the translation domain is the application name:
    settings.setdefault('genshi.translation_domain', config.registry.__name__)
    # TODO: Evaluate pyramid_genshi which maps to TranslationString calls.

    # The renderer must be available to views so fragment templates can be
    # rendered. So we store it in the settings object:
    renderer = settings['genshi_renderer'] = GenshiTemplateRenderer(settings)

    def factory(info):
        '''info.name is the value passed by the user as the renderer name.

        info.package is the "current package" when the renderer configuration
        statement was found.

        info.type is the renderer type name, i.e. ".genshi".

        info.registry is the "current" application registry when
        the renderer was created.

        info.settings is the ISettings dictionary related to the current app.
        '''
        return renderer
    extension = settings.get('genshi.extension', '.genshi')
    config.add_renderer(extension, factory)
