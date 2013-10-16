# --------------------------------------------------------------------
from setuptools import setup, find_packages

# --------------------------------------------------------------------
requires = [
    'pyramid >=1.4, <1.5',
    'pyramid_debugtoolbar',
    'genshi >=0.7',
    'waitress',
    'gevent ==1.0dev',
    'gevent-websocket ==0.4',
]

classifiers = [
    "Programming Language :: Python",
    "Framework :: Pyramid",
    "Topic :: Internet :: WWW/HTTP",
    "Topic :: Internet :: WWW/HTTP :: WSGI :: Application",
]

ENTRY_POINTS = """\
[paste.app_factory]
main = econline:main
"""

XDEPS = [
    'https://bitbucket.org/Jeffrey/gevent-websocket/get/default.tar.bz2#egg=gevent-websocket-0.4',
    'https://github.com/surfly/gevent/tarball/1.0rc3#egg=gevent-1.0dev',
]

# --------------------------------------------------------------------
setup(name='econline',
      version='0.1',
      description='econline',
      long_description='EasyCrypt Online',
      classifiers=classifiers,
      author='EasyCrypt Team',
      author_email='admin@easycrypt.info',
      url='http://ci.easycrypt.info',
      keywords='easycrypt online web',
      packages=find_packages(),
      dependency_links=XDEPS,
      include_package_data=True,
      zip_safe=False,
      install_requires=requires,
      tests_require=requires,
      test_suite="econline",
      entry_points=ENTRY_POINTS)
