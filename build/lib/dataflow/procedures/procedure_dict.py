import logging
import os

l = logging.getLogger(name=__name__)

from angr.misc import autoimport
# from ..sim_procedure import SimProcedure

# Import all classes under the current directory, and group them based on
# lib names.
SIM_PROCEDURES = {}
path = os.path.dirname(os.path.abspath(__file__))
skip_dirs = ['__pycache__', 'definitions', 'stubs']
# print('Path: %s' % (path))

for pkg_name, package in autoimport.auto_import_packages('dataflow.procedures', path, skip_dirs):
    SIM_PROCEDURES[pkg_name] = {}
    # print(pkg_name, package)
    for _, mod in autoimport.filter_module(package, type_req=type(os)):
        # print(mod)
        for name, proc in autoimport.filter_module(mod, type_req=type):
            # print(name, proc)
            SIM_PROCEDURES[pkg_name][name] = proc
            if name == 'UnresolvableJumpTarget':
                SIM_PROCEDURES[pkg_name]['UnresolvableTarget'] = proc

class _SimProcedures(object):
    def __getitem__(self, k):
        l.critical("the SimProcedures dictionary is DEPRECATED. Please use the angr.SIM_PROCEDURES global dict instead.")
        return SIM_PROCEDURES[k]

    def __setitem__(self, k, v):
        l.critical("the SimProcedures dictionary is DEPRECATED. Please use the angr.SIM_PROCEDURES global dict instead.")
        SIM_PROCEDURES[k] = v
SimProcedures = _SimProcedures()
