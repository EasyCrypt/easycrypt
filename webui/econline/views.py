# --------------------------------------------------------------------
from pyramid.view import view_config
import pyramid.httpexceptions as exc

# --------------------------------------------------------------------
ECCODE = '''\
require import Int.

op myop(x y z : int) : int = x * y + z.

theory T.

op inside(x y z : int) : int = x * y + z.

end T

op mysecondop(x y z : int) : int = x * y + z.

lemma L x y z: myop x y z = x * y + z.
proof.
  smt.
qed.
'''

# --------------------------------------------------------------------
class View(object):
    def __init__(self, context, request):
        self.context = context
        self.request = request

    @view_config(route_name='home', renderer='econline:templates/index.genshi')
    def home(self):
        return {}

    @view_config(route_name='tryme', renderer='econline:templates/tryme.genshi')
    def tryme(self):
        settings = self.request.registry.settings
        engine   = settings.get('econline.engine')

        if engine is None:
            raise exc.HTTPInternalServerError()

        return dict(eccode = ECCODE, engine = engine)
