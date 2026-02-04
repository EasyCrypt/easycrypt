# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

import logging
import os
import pathlib
import sys

from docutils.parsers.rst import roles
from sphinx.util import logging as sphinx_logging
from sphinx.roles import code_role

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'EasyCrypt refman'
copyright = '2026, EasyCrypt development team'
author = 'EasyCrypt development team'

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

EXTENSIONS = pathlib.Path('extensions').resolve()
for x in ['ecpygment', 'ecproofs']:
  sys.path.append(str(EXTENSIONS / x))

extensions = [
  'sphinx_rtd_theme',
  'sphinx_design',
  'ecpygment',
  'ecproofs',
]

highlight_language = 'easycrypt'
default_role = 'easycrypt'

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# -- EasyCrypt proofs -------------------------------------------------------

ecproofs_cache_dir = '../ecproofs/cache'
ecproofs_scripts_dir = '../ecproofs/scripts'

# -- EasyCrypt proofs logging ----------------------------------------------

_ecproofs_store_level = os.getenv('ECPROOFS_STORE_LOG_LEVEL', 'INFO').upper()
_ecproofs_store_logger = sphinx_logging.getLogger('ecproofs.store')
_ecproofs_store_logger.setLevel(getattr(logging, _ecproofs_store_level, logging.INFO))

_ecproofs_cache_level = os.getenv('ECPROOFS_CACHE_LOG_LEVEL', 'INFO').upper()
_ecproofs_cache_logger = sphinx_logging.getLogger('ecproofs.cache')
_ecproofs_cache_logger.setLevel(getattr(logging, _ecproofs_cache_level, logging.INFO))

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']
html_css_files = [
  'easycrypt.css',
]

# -- EasyCrypt role ----------------------------------------------------------
def _easycrypt_role(name, rawtext, text, lineno, inliner, options=None, content=()):
  options = {} if options is None else options.copy()
  options['language'] = 'easycrypt'
  return code_role(name, rawtext, text, lineno, inliner, options, content)

# -- Setup app ---------------------------------------------------------------
def setup(app):
  app.add_role('easycrypt', _easycrypt_role)
