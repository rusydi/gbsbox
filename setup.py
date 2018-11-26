## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests


# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib -m 0 gbsbox")
        if errno != 0:
            sys.exit(1)

setup(
    name = "gbsbox",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='GBSBox - SageMath Package to Analyze SBox using Grobner Bases',
    long_description = readfile("README.rst"), # get the long description from the README
    url='https://github.com/rusydi/gbsbox',
    author='Rusydi H. Makarim',
    author_email='rusydi@pm.me', # choose a main contact email
    license='GPLv2+', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 3 - Alpha',
      'Intended Audience :: Science/Research',
      'Topic :: Software Development :: Build Tools',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)',
      'Programming Language :: Python :: 2.7',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "SageMath packaging",
    packages = ['gbsbox'],
    cmdclass = {'test': SageTest}, # adding a special setup command for tests
    setup_requires   = ['sage-package'],
    install_requires = ['sage-package', 'sphinx'],
)
