import pycparser.c_ast as csyn
from asthelper import *

# integer type: ('int', bitwidth)
# pointer type: ('ptr', bitwidth of element)

class SymBinaryExpr:
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right
        # e.g. SymBinExpr('+', 'a', 1)

class SymUnaryExpr:
    def __init__(self, op, e):
        self.op = op
        self.expr = e
        # e.g. SymUnaryExpr('-', 'a')

class SymPtr:
    def __init__(self, base):
        self.base = base
        self.offset = 0
        # SymPtr(index of ExecContext.allocated_arrays, element offset)

class SymFunCall:
    def __init__(self, func, args):
        self.func = func
        self.args = args

# constraints are represented by 3-tuple (op, symexpr, symexpr)
#   like ('>=', SymBinExpr('+', 'm', 1), 'n')

class ExecContext:
    def __init__(self):
        self.progvar_binds = dict()
        self.path_conditions = []
        self.allocated_arrays = []
        self.progvar_types = dict()
        self.symvar_types = dict()
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