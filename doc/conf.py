# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

import pathlib
import sys

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

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']
