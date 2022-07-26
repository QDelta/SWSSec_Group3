from copy import deepcopy
from collections import namedtuple
import pycparser.c_ast as csyn
from asthelper import *
import z3

# Generate unique name for variables.
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

def toint(v):
    if z3.is_bv(v):
        return z3.BV2Int(v, is_signed=True)
    else:
        return v

class SymExecError(Exception):
    def __init__(self, msg: str):
        self.msg = msg

# * values * #
IntVal = namedtuple('IntVal', ['val'])
IntPtrVal = namedtuple('IntPtrVal', ['low', 'high'])

class ExecContext:
    def __init__(self, params, assumes):
        self.env = dict()
        self.path_cond = True
        self.__init_env(params)
        self.__init_path_cond(assumes)

    # Initialize the environment from params through pycparser.
    def __init_env(self, params):
        for pname, typ in params:
            if typ == 'int':
                self.__decl_int(pname)
            elif typ == 'ptr':
                high_name = NAME_GEN.new_name(f'{pname}_capacity')
                high = z3.Int(high_name)
                self.__decl_intptr(pname, init=IntPtrVal(0, high))
                self.__add_assume(high >= 0)

    # Initialize the path condition P_0 from assumes through pycparser.
    def __init_path_cond(self, assumes):
        for assume in assumes:
            self.__add_assume(self.__parse_condition(assume, in_assume=True))

    def __add_assume(self, a):
        self.path_cond = z3.And(self.path_cond, a)

    # Parse condition into z3 Bool.
    def __parse_condition(self, cond: csyn.Node, in_assume=False):
        if isinstance(cond, csyn.UnaryOp):
            if cond.op == '!':
                return z3.Not(self.__parse_condition(cond.expr))
            else:
                raise SymExecError(f"Unsupported unary operator in condition: {cond.op}")
        if isinstance(cond, csyn.BinaryOp):
            if cond.op in ['>', '>=', '<', '<=', '==', '!=']:
                lval = self.eval(cond.left, in_assume=in_assume)
                rval = self.eval(cond.right, in_assume=in_assume)
                if isinstance(lval, IntVal) and isinstance(rval, IntVal):
                    lval, rval = toint(lval.val), toint(rval.val)
                    if cond.op == '>':
                        return lval > rval
                    elif cond.op == '>=':
                        return lval >= rval
                    elif cond.op == '<':
                        return lval < rval
                    elif cond.op == '<=':
                        return lval <= rval
                    elif cond.op == '==':
                        return lval == rval
                    else: # cond.op == '!='
                        return lval != rval
                else:
                    raise SymExecError('Integer comparsion operator applied to non-integers')
            elif cond.op in ['&&', '||']:
                lcond = self.__parse_condition(cond.left)
                rcond = self.__parse_condition(cond.right)
                if cond.op == '&&':
                    return z3.And(lcond, rcond)
                else: # cond.op == '||'
                    return z3.Or(lcond, rcond)
            else:
                raise SymExecError(f"Unsupported binary operator in condition: {cond.op}")
        else:
            raise SymExecError(f"Unsupported condition: {cond}")

    # evaluation: returns either IntVal or PtrVal
    def eval(self, expr: csyn.Node, in_assume=False):
        # Evaluate integer literal
        if isinstance(expr, csyn.Constant):
            if expr.type == 'int':
                if in_assume:
                    return IntVal(z3.IntVal(expr.value))
                else:
                    return IntVal(z3.BitVecVal(expr.value, 32))
            else:
                raise SymExecError(f"Unsupported constant type: {expr.type}")

        # Evaluate name
        elif isinstance(expr, csyn.ID):
            if expr.name not in self.env:
                raise SymExecError(f"Undeclared variable: {expr.name}")

            return self.env[expr.name]

        # Evaluate unary operation:
        elif isinstance(expr, csyn.UnaryOp):
            if expr.op == '+':
                return self.eval(expr.expr)
            elif expr.op == '-':
                val = self.eval(expr.expr)
                if isinstance(val, IntVal):
                    return IntVal(-val.val)
                else:
                    raise SymExecError(f"Can not apply '-' to {expr}")
            else:
                raise SymExecError(f"Unsupported unary operator {expr.op}")

        # Evaluate binary operation:
        elif isinstance(expr, csyn.BinaryOp):
            left = self.eval(expr.left)
            right = self.eval(expr.right)
            if isinstance(left, IntVal) and isinstance(right, IntVal):
                lval = left.val
                rval = right.val
                op = expr.op
                return self.eval_int_binop(op, lval, rval)

            # Evaluate calculation between Ptr and Int:
            elif isinstance(left, IntVal) and isinstance(right, IntPtrVal):
                if expr.op == '+':
                    return IntPtrVal(right.low - toint(left.val),
                                     right.high - toint(left.val))
                else:
                    raise SymExecError(f"Can not apply '{op}' to integer and pointer")
            elif isinstance(left, IntPtrVal) and isinstance(right, IntVal):
                if expr.op == '+':
                    return IntPtrVal(left.low - toint(right.val),
                                     left.high - toint(right.val))
                elif expr.op == '-':
                    return IntPtrVal(left.low + toint(right.val),
                                     left.high + toint(right.val))
                else:
                    raise SymExecError(f"Can not apply '{op}' to integer and pointer")

        # Evaluate memory allocation:
        elif isinstance(expr, csyn.FuncCall):
            func = expr.name
            args = expr.args.exprs
            if isinstance(func, csyn.ID):
                fname = func.name
                if in_assume:
                    if fname != 'capacity':
                        raise SymExecError(f"Unsupported function {fname} in assumption")
                    if len(args) != 1:
                        raise SymExecError(f"'capacity' expects 1 argument, given {len(args)}")
                    ptr = self.eval(args[0])
                    if isinstance(ptr, IntPtrVal):
                        return IntVal(ptr.high)
                    else:
                        raise SymExecError(f"'capacity' expects pointer, given {args[0]}")
                else:
                    if fname != 'alloc':
                        raise SymExecError(f"Unsupported function {fname} in assumption")
                    if len(args) != 1:
                        raise SymExecError(f"'malloc' expects 1 argument, given {len(args)}")
                    cap = self.eval(args[0])
                    if isinstance(cap, IntVal):
                        return IntPtrVal(0, toint(cap.val))
                    else:
                        raise SymExecError(f"'alloc' expects integer, given {args[0]}")
            else:
                raise SymExecError(f"Unsupported non-identifier function call: {func}")

        else:
            raise SymExecError(f"Unsupported expr: {expr}")

    @staticmethod
    def eval_int_binop(op: str, left, right):
        if op == '+':
            return IntVal(left + right)
        elif op == '-':
            return IntVal(left - right)
        elif op == '*':
            return IntVal(left * right)
        elif op == '%':
            return IntVal(left % right)
        elif op == '/':
            if isinstance(left, int) and isinstance(right, int):
                return IntVal(left // right)
            else:
                return IntVal(left / right)

    # execution: returns list of counter examples
    def exec(self, stmt: csyn.Node) -> list:
        # Exec decl stmt:
        if isinstance(stmt, csyn.Decl):
            if stmt.init:
                init_val = self.eval(stmt.init)
            else:
                init_val = None

            decl_typ = decl_to_type(stmt.type)
            if decl_typ == 'int':
                self.__decl_int(stmt.name, init=init_val)
            elif decl_typ == 'ptr':
                self.__decl_intptr(stmt.name, init=init_val)
            
            return []

        # Exec assign stmt:
        elif isinstance(stmt, csyn.Assignment):
            if isinstance(stmt.lvalue, csyn.ID):
                vname = stmt.lvalue.name
                if stmt.lvalue.name not in self.env:
                    raise SymExecError(f"Undeclared identifier {vname}")
                self.env[vname] = self.eval(stmt.rvalue)
            else:
                raise SymExecError(f"Unsupported left-side of assignment: {stmt.lvalue}")
            
            return []

        # Exec access stmt:
        elif isinstance(stmt, csyn.FuncCall):
            if isinstance(stmt.name, csyn.ID):
                if stmt.name.name == 'print':
                    arg = stmt.args.exprs[0]
                    if isinstance(arg, csyn.ArrayRef):
                        ptr = self.eval(arg.name)
                        idx = self.eval(arg.subscript)

                        if isinstance(ptr, IntPtrVal) and isinstance(idx, IntVal):
                            return [(z3.And(self.path_cond, z3.Or(ptr.low > toint(idx.val), toint(idx.val) >= ptr.high)), arg.coord.line)]

                        else:
                            raise SymExecError("Array subscript expect pointer[integer]")
            raise SymExecError(f"Unsupported statement: {stmt}")

        # Exec sequence stmt:
        elif isinstance(stmt, csyn.Compound):
            ce_list = []
            for s in stmt.block_items:
                ce_list += self.exec(s)
            return ce_list

        # Exec if-then stmt:
        elif isinstance(stmt, csyn.If):
            cond = self.__parse_condition(stmt.cond)
            ce_list = []

            true_ctx = deepcopy(self)
            true_ctx.__add_assume(cond)
            ce_list += true_ctx.exec(stmt.iftrue)

            false_ctx = deepcopy(self)
            false_ctx.__add_assume(z3.Not(cond))
            ce_list += false_ctx.exec(stmt.iffalse)

            new_env = self.__merge_env(cond, true_ctx.env, false_ctx.env)
            self.env = new_env

            return ce_list
        else:
            raise SymExecError(f"Unsupported statement: {stmt}")

    def __decl_int(self, var_name, init=None):
        if var_name in self.env:
            raise SymExecError(f"Duplicate declaration of {var_name}")

        if init:
            self.env[var_name] = init
        else:
            logical_name = NAME_GEN.new_name(var_name)
            sym_val = z3.BitVec(logical_name, 32)
            self.env[var_name] = IntVal(sym_val)

    def __decl_intptr(self, var_name, init=None):
        if var_name in self.env:
            raise SymExecError(f"Duplicate declaration of {var_name}")
        
        if init:
            self.env[var_name] = init
        else:
            self.env[var_name] = IntPtrVal(0, 0)

    # merge context of two branches
    @staticmethod
    def __merge_env(a, env1: dict, env2: dict):
        new_env = dict()
        for x in env1:
            if x in env2:
                v1 = env1[x]
                v2 = env2[x]
                if isinstance(v1, IntVal) and isinstance(v2, IntVal):
                    new_env[x] = IntVal(z3.If(a, v1.val, v2.val))
                elif isinstance(v1, IntPtrVal) and isinstance(v2, IntPtrVal):
                    new_env[x] = IntPtrVal(z3.If(a, v1.low, v2.low),
                                           z3.If(a, v1.high, v2.high))
                else:
                    raise SymExecError(f"{x} is assigned to different types of value in two branches")
        return new_env
