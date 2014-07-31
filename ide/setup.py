#! /usr/bin/env python3

# --------------------------------------------------------------------
from setuptools import setup

# --------------------------------------------------------------------
ENTRY_POINTS = {
    'gui_scripts': [
        'ecide = ec.ecide.main',
    ]
}

setup(
    name         = 'easycrypt.gui',
    version      = '0.1',
    description  = 'GUI for the EasyCrypt Proof Assistant',
    author       = 'EasyCrypt Term',
    author_email = 'admin@easycrypt.info',
    package_dir  = {'': 'src'},
    packages     = ['json'],
    entry_points = ENTRY_POINTS,
)
