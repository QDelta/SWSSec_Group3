from collections import namedtuple
import pycparser.c_ast as csyn
from asthelper import *
import z3

# integer type: ('int', bytewidth)
# pointer type: ('ptr', bytewidth of element)

# values
IntVal = namedtuple('IntVal', ['val'])
PtrVal = namedtuple('PtrVal', ['low', 'high'])

# use z3 corresponding components for other definitions
# like ite -> z3.If

class ExecContext:
    def __init__(self):
        self.environment = dict()
        self.path_condition = True
        self.progvar_types = dict()
        self.name_gen = NameGenerator() # generating names of symvars

    # merge context of two branches
    @staticmethod
    def merge(ctx1, ctx2):
        pass

    def expr_to_sym_expr(self, expr):
        pass

    def exec(self, stmt):
        pass

class NameGenerator:
    def __init__(self):
        self.mem = dict()

    def new_name(self, base: str):
        if base in self.mem:
            idx = self.mem[base]
            self.mem[base] = idx + 1
            return base + f"#{idx}"
        else:
            self.mem[base] = 0
            return base