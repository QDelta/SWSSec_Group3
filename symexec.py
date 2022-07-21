from collections import namedtuple
from copy import deepcopy
import pycparser.c_ast as csyn
from asthelper import *
import z3

# integer type: ('int', bytewidth)
# pointer type: ('ptr', bytewidth of element)

# values
IntVal = namedtuple('IntVal', ['val'])
PtrVal = namedtuple('PtrVal', ['low', 'high', 'bytewidth'])

# use z3 corresponding components for other definitions
# like ite -> z3.If

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

NAME_GEN = NameGenerator()

class ExecContext:
    def __init__(self):
        self.env = dict()

    # returns either IntVal or PtrVal
    def eval(self, expr):
        pass

    def __decl_int(self, var_name, bytewidth):
        if var_name in self.env:
            raise Exception("")

        logical_name = NAME_GEN.new_name(var_name)
        sym_val = z3.BitVec(logical_name, 8 * bytewidth)
        self.env[var_name] = IntVal(sym_val)

    def __decl_ptr(self, var_name, bytewidth):
        if var_name in self.env:
            raise Exception("")

        self.env[var_name] = PtrVal(0, 0, bytewidth)

    # merge context of two branches
    def __merge(self, v, other):
        new_env = dict()
        for x in self.env:
            if x in other.env:
                v1 = self.env[x]
                v2 = other.env[x]
                if isinstance(v1, IntVal) and isinstance(v2, IntVal):
                    new_env[x] = IntVal(z3.If(v==0, v2.val, v1.val))
                elif isinstance(v1, PtrVal) and isinstance(v2, PtrVal):
                    new_env[x] = PtrVal(z3.If(v==0, v2.low, v1.low), z3.If(v==0, v2.high, v1.high))
                else:
                    raise Exception("")
        self.env = new_env

    # returns list of counter examples
    def exec(self, path_condition, stmt):
        pass