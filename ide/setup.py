#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, os, cx_Freeze as setup

# --------------------------------------------------------------------
base    = "Win32GUI" if sys.platform == "win32" else None
thisdir = os.path.realpath(os.path.dirname(__file__))

# --------------------------------------------------------------------
data = [('ec/data/', 'data/'), ('binaries/', './')]

# --------------------------------------------------------------------
exe = setup.Executable(
    'ec/entry.py',
    base         = base,
    path         = sys.path+[thisdir],
    targetName   = 'easycrypt-ide',
    compress     = False,
    shortcutName = 'EasyCrypt Editor',
    shortcutDir  = 'easycrypt',
)

# --------------------------------------------------------------------
build_exe_options = dict(packages = ['os', 'ec'], include_files = data)

# --------------------------------------------------------------------
def _do_pyrcc():
    import ec.ecide; ec.ecide.main(forbuild = True)

_do_pyrcc()

# --------------------------------------------------------------------
setup.setup(
    name         = 'easycrypt.gui',
    version      = '0.1',
    description  = 'GUI for the EasyCrypt Proof Assistant',
    author       = 'EasyCrypt Term',
    author_email = 'team@easycrypt.info',
    packages     = ['ec'],
    options      = dict(build_exe = build_exe_options),
    executables  = [exe],
)
