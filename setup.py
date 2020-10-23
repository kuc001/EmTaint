try:
    from setuptools import setup
    from setuptools import find_packages
    packages = find_packages()
except ImportError:
    from distutils.core import setup
    import os
    packages = [x.strip('./').replace('/','.') for x in os.popen('find -name "__init__.py" | xargs -n1 dirname').read().strip().split('\n')]

setup(
    name='dataflow',
    version='1.0.0.0',
    packages=packages,
    install_requires=[
        'angr',
    ],
    description="A compatibility layer for dataflow's removal.",
    url='https://gitlab.com/DoneingCK/dataflow.git',
)
