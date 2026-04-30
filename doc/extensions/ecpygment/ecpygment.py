# --------------------------------------------------------------
import sphinx.application as sa
import sphinx.util        as su

from lexers.easycrypt import EasyCryptLexer

# --------------------------------------------------------------
def setup(app: sa.Sphinx) -> su.typing.ExtensionMetadata:
  app.add_lexer("easycrypt", EasyCryptLexer)

  return {
    'version': '0.1',
    'parallel_read_safe': True,
    'parallel_write_safe': True,
  }
