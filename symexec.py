from copy import deepcopy
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


# * values * #
# character type: ('char', val, bitwidth)
# integer   type: ('int',  val, bitwidth)
# pointer   type: ('ptr',  low, high, bitwidth of element)


class ChrVal:
    def __init__(self, val: z3.CharRef, bitwidth):
        self.val = val
        self.bitwidth = bitwidth

    def __str__(self):
        return f"ChrVal(val={self.val}, bitwidth={self.bitwidth})"


class IntVal:
    def __init__(self, val, bitwidth):
        self.val = val  # val: z3.IntNumRef or z3.BitVecRef
        self.bitwidth = bitwidth

    def __str__(self):
        return f"IntVal(val={self.val}, bitwidth={self.bitwidth})"


class PtrVal:
    def __init__(self, low, high, bitwidth):
        self.low = low
        self.high = high  # type can be int, z3.BitVec('a', 32) -> a var.
        self.bitwidth = bitwidth  # It is the bitwidth of pointed element.

    def __str__(self):
        return f"PtrVal(low={self.low}, high={self.high}, bitwidth of element={self.bitwidth})"


# use z3 corresponding components for other definitions
# like:
# z3.IntVal(val)
# z3.BitVec(name, bv)
# -z3.IntVal(100)
# z3.BitVec('a', 32) [+-*/%] z3.BitVec('b', 32)
# ite -> z3.If(cond, a, b)

# * assertions * #
# use z3 corresponding components for other definitions
# like:
# z3.IntVal(1) < z3.IntVal(100)
# z3.Not(a)
# z3.And(*args)
# z3.Or(*args)


class ExecContext:
    def __init__(self, params, assumes, body):
        self.env = dict()
        self.path_cond = list()  # ----------> Pretend path conditions are all 'And' together.
        self.body = body
        self.__init_env(params)
        self.__init_path_cond(assumes)

    # Use z3 to check the program.
    def check(self):
        solver = z3.Solver()
        unchecked = z3.And([cond for cond in self.path_cond])
        solver.add(unchecked)
        res = solver.check()
        if res == z3.sat:
            print(f'The result: {res}\nThe model: {solver.model()}')
        else:
            print(f'The result: {res}')

    # Run the program.
    def run(self):
        for stmt in self.body:
            self.exec(stmt)
            self.print_env()
            self.print_path_cond()

    # Print out the current environment.
    def print_env(self):
        print('-------------- Environment ---------------')
        for k, v in self.env.items():
            print(f'Key = {k}, Value = {v}')
        print('------------------------------------------\n')

    # Print out the current path condition.
    def print_path_cond(self):
        print('------------- Path Condition -------------')
        print(z3.And([cond for cond in self.path_cond]))
        print('------------------------------------------\n')

    # Initialize the environment E_0 from params through pycparser.
    # params[i] = ('var_nam', ('int|ptr', bitwidth))
    # -> self.env['var_name'] = IntVal(z3.IntVal, bitwidth) instance
    # -> self.env['var_name'] = PrtVal(low, high, bitwidth) instance
    def __init_env(self, params: list[tuple[tuple]]):
        for param in params:
            if param[1][0] == 'int':
                self.__decl_int_var(param[0], param[1][1])
            elif param[1][0] == 'ptr':
                self.__decl_ptr_var_with_lh(param[0], 0, z3.BitVec(param[0], param[1][1]), param[1][1])

    # Initialize the path condition P_0 from assumes through pycparser.
    def __init_path_cond(self, assumes: list[csyn.Node]):
        for assume in assumes:
            self.path_cond.append(self.__parse_assume(assume))

    # Parse assume into path condition.
    def __parse_assume(self, assume: csyn.Node):
        if isinstance(assume, csyn.ID):  # Identifier, no more recursion. (???bitwidth no known)
            # ID -> sometimes like ID = 3; sometimes func(ID) ...
            return z3.BitVec(assume.name, 4 * 8)  # ----------------------> FURTHER MODIFICATION <----------------------
        elif isinstance(assume, csyn.Constant):  # Constant, no more recursion.
            if assume.type == 'int':
                logical_name = NAME_GEN.new_name(assume.type)
                sym_val = z3.BitVec(logical_name, 32)
                self.path_cond.append(sym_val == assume.value)
                return sym_val
            elif assume.type == 'char':
                logical_name = NAME_GEN.new_name(assume.type)
                sym_val = z3.BitVec(logical_name, 8)
                self.path_cond.append(sym_val == assume.value)
                return sym_val
        elif isinstance(assume, csyn.UnaryOp):  # Unary Operation(- +), recursion needed.
            if assume.op == '+':
                return +self.__parse_assume(assume.expr)
            elif assume.op == '-':
                return -self.__parse_assume(assume.expr)
            elif assume.op == 'sizeof':
                pass  # return the size of expr; -----------------> maybe need to use another parameter -> bitwidth
        elif isinstance(assume, csyn.BinaryOp):  # Binary Operation, recursion needed.
            # lval and rval might happen: BitVecRef and IntValRef cannot concat with > < - +.
            if assume.op == '>':
                return self.__parse_assume(assume.left) > self.__parse_assume(assume.right)
            elif assume.op == '>=':
                return self.__parse_assume(assume.left) >= self.__parse_assume(assume.right)
            elif assume.op == '<':
                return self.__parse_assume(assume.left) < self.__parse_assume(assume.right)
            elif assume.op == '<=':
                return self.__parse_assume(assume.left) <= self.__parse_assume(assume.right)
            elif assume.op == '==':
                return self.__parse_assume(assume.left) == self.__parse_assume(assume.right)
        elif isinstance(assume, csyn.FuncCall):  # Function Call, ExprList recursion needed.
            pass  # Unimplemented...

    # evaluation: returns either ChrVal or IntVal or PtrVal
    def eval(self, expr: csyn.Node) -> object:
        # 1. Evaluate integer literal, name:
        if isinstance(expr, csyn.Constant):
            if expr.type == 'int':
                return IntVal(z3.IntVal(expr.value), 32)
            elif expr.type == 'char':
                return ChrVal(z3.CharVal(expr.value[1]), 8)  # expr.value = "'c'" -> get only `c`

        elif isinstance(expr, csyn.ID):
            if expr.name not in self.env:  # var in the right value is not in E.
                raise Exception("Undeclared variable!!!")

            return self.env[expr.name]  # return value can be ChrVal, IntVal, PtrVal.

        # 2. Evaluate unary operation:
        elif isinstance(expr, csyn.UnaryOp):
            pass

        # 3. Evaluate binary operation:
        elif isinstance(expr, csyn.BinaryOp):
            left = self.eval(expr.left)
            right = self.eval(expr.right)
            if isinstance(left, IntVal) and isinstance(right, IntVal):
                return self.eval_int_binop(left, right, expr.op)
        # 4. Evaluate calculation between Ptr and Int:
            elif (isinstance(left, IntVal) and isinstance(right, PtrVal)) \
                    or (isinstance(left, PtrVal) and isinstance(right, IntVal)):
                pass

        # [X] 4. Evaluate calculation between Ptr and Int:
        # elif isinstance(expr, csyn.ArrayRef):  # make this as stmt handling.
        #     pass

        # 5. Evaluate memory allocation:
        # elif isinstance(expr, csyn.Node):
        #     pass

    # evaluation: IntVal binop IntVal
    @staticmethod
    def eval_int_binop(left: IntVal, right: IntVal, op: str):
        if isinstance(left.val, z3.IntNumRef) and isinstance(right.val, z3.IntNumRef):  # const binop const
            lval = left.val.as_long()
            rval = right.val.as_long()
            if op == '+': return IntVal(z3.IntVal(lval + rval), 32)
            elif op == '-': return IntVal(z3.IntVal(lval - rval), 32)
            elif op == '*': return IntVal(z3.IntVal(lval * rval), 32)
            elif op == '/': return IntVal(z3.IntVal(lval / rval), 32)  # Unimplemented: integer division in C code.
            elif op == '%': return IntVal(z3.IntVal(lval % rval), 32)
            elif op == '==':
                pass  # Boolean eval temporarily unimplemented.

        elif isinstance(left.val, z3.BitVecRef):  # var binop const
            if op == '+': return IntVal(left.val + right.val.as_long(), 32)
            elif op == '-': return IntVal(left.val - right.val.as_long(), 32)
            elif op == '*': return IntVal(left.val * right.val.as_long(), 32)
            elif op == '/': return IntVal(left.val / right.val.as_long(), 32)  # Unimplemented: integer division in C.
            elif op == '%': return IntVal(left.val % right.val.as_long(), 32)
            elif op == '==':
                pass  # Boolean eval temporarily unimplemented.

        elif isinstance(right.val, z3.BitVecRef):  # const binop var
            if op == '+': return IntVal(left.val.as_long() + right.val, 32)
            elif op == '-': return IntVal(left.val.as_long() - right.val, 32)
            elif op == '*': return IntVal(left.val.as_long() * right.val, 32)
            elif op == '/': return IntVal(left.val.as_long() / right.val, 32)  # Unimplemented: integer division in C.
            elif op == '%': return IntVal(left.val.as_long() % right.val, 32)
            elif op == '==':
                pass  # Boolean eval temporarily unimplemented.

        else:  # var binop var
            if op == '+': return IntVal(left.val + right.val, 32)
            elif op == '-': return IntVal(left.val - right.val, 32)
            elif op == '*': return IntVal(left.val * right.val, 32)
            elif op == '/': return IntVal(left.val / right.val, 32)  # Unimplemented: integer division in C.
            elif op == '%': return IntVal(left.val % right.val, 32)
            elif op == '==':
                pass  # Boolean eval temporarily unimplemented.

    # evaluation: especially for the condition of 'if' statement.
    def eval_cond(self, expr: csyn.Node) -> z3.BoolRef:
        pass

    # execution: returns list of counter examples
    def exec(self, stmt: csyn.Node):
        # 1. Exec skip stmt:
        if stmt is None:
            return

        # 2. Exec decl stmt:
        elif isinstance(stmt, csyn.Decl):
            # var_name = stmt.name
            # init_val = eval(stmt.init)
            if isinstance(stmt.type, csyn.TypeDecl):
                # identifier_type = stmt.type.type.names  # -> ['int']
                if stmt.init is not None:  # Declaration with initialization.
                    if stmt.type.type.names == ['char']:
                        self.__decl_char(stmt.name, chr(int(str(self.eval(stmt.init).val))), 8)  # un-tested!!!
                    elif stmt.type.type.names == ['int']:
                        self.__decl_int(stmt.name, self.eval(stmt.init).val.as_long(), 32)
                else:
                    if stmt.type.type.names == ['char']:
                        self.__decl_char(stmt.name, 0, 8)
                    elif stmt.type.type.names == ['int']:
                        self.__decl_int(stmt.name, 0, 32)
            elif isinstance(stmt.type, csyn.PtrDecl):  # Prt -> int or char.
                # element's identifier_type = stmt.type.type.type.names  # -> ['int']
                if stmt.init is not None:  # Declaration with initialization.
                    ptr_val = self.eval(stmt.init)  # stmt.init is the instance of csyn.ID class.
                    self.__decl_ptr_var_with_lh(stmt.name, ptr_val.low, ptr_val.high, ptr_val.bitwidth)
                else:
                    if stmt.type.type.type.names == ['char']:
                        self.__decl_ptr_var(stmt.name, 8)
                    elif stmt.type.type.type.names == ['int']:
                        self.__decl_ptr_var(stmt.name, 32)

        # 3. Exec assign stmt:
        elif isinstance(stmt, csyn.Assignment):
            if stmt.lvalue.name not in self.env:
                raise Exception("Undeclared left_value!!!")

            self.env[stmt.lvalue.name] = self.eval(stmt.rvalue)

        # 4. Exec access stmt:
        elif isinstance(stmt, csyn.ArrayRef):
            if stmt.name.name not in self.env:
                raise Exception("Undeclared pointer!!!")

            # Check the bound of ptr. (ind: IntVal(val = z3.IntNumRef or z3.BitVecRef); ptr: PtrVal)
            ind = self.eval(stmt.subscript)
            ptr = self.env[stmt.name.name]
            if isinstance(ind.val, z3.IntNumRef):
                self.path_cond.append(z3.And(ptr.low <= ind.val.as_long(), ind.val.as_long() < ptr.high))
            elif isinstance(ind.val, z3.BitVecRef):
                self.path_cond.append(z3.And(ptr.low <= ind.val, ind.val < ptr.high))

            # [X]
            # if ptr.low <= ind < ptr.high:
            #     raise Exception("Array access out of bounds!!!")
            #
            # self.path_cond.append(z3.Or(ind < ptr.low, ptr.high <= ind))

        # 5. Exec sequence stmt:
        elif isinstance(stmt, csyn.Compound):
            for a_stmt in stmt.block_items:
                self.exec(a_stmt)

        # 6. Exec if-then stmt:
        elif isinstance(stmt, csyn.If):
            # -------------- Expired --------------
            # cond instance of a designed class (XXX), two attributes:
            #   true_cond_path: []
            #   false_cond_path: []
            # -------------- Expired --------------
            z3cond = self.eval_cond(stmt.cond)  # convert into a z3 boolean value.
            iftrue = self.exec(stmt.iftrue)  # instance of csyn.Compound; its block_items have
            iffalse = self.exec(stmt.iffalse)
            # If Statement handling:
            self.path_cond.append(z3.If(z3cond, iftrue, iffalse))  # [X]
            # ? straightly append it into path_cond or as formula
            # -> divided into two path conditions to check.

        # 7. Return stmt:
        elif isinstance(stmt, csyn.Return):
            # the program will end here.
            if isinstance(stmt.expr, csyn.ArrayRef):
                return self.exec(stmt.expr)
            else:
                return self.eval(stmt.expr)

    """Helper Methods"""

    def __decl_char(self, var_name, val, bitwidth=1 * 8):
        if var_name in self.env:
            raise Exception("Duplicate Declaration!!!")

        sym_val = z3.CharVal(val)
        self.env[var_name] = ChrVal(sym_val, bitwidth)

    def __decl_char_var(self, var_name, bitwidth=1 * 8):
        if var_name in self.env:
            raise Exception("Duplicate Declaration!!!")

        logical_name = NAME_GEN.new_name(var_name)
        sym_val = z3.BitVec(logical_name, bitwidth)
        self.env[var_name] = ChrVal(sym_val, bitwidth)

    def __decl_int(self, var_name, val, bitwidth=4 * 8):
        if var_name in self.env:
            raise Exception("Duplicate Declaration!!!")

        sym_val = z3.IntVal(val)
        self.env[var_name] = IntVal(sym_val, bitwidth)

    def __decl_int_var(self, var_name, bitwidth=4 * 8):
        if var_name in self.env:
            raise Exception("Duplicate Declaration!!!")

        logical_name = NAME_GEN.new_name(var_name)
        sym_val = z3.BitVec(logical_name, bitwidth)
        self.env[var_name] = IntVal(sym_val, bitwidth)

    def __decl_ptr_var(self, var_name, bitwidth):
        if var_name in self.env:
            raise Exception("Duplicate Declaration!!!")

        self.env[var_name] = PtrVal(0, 0, bitwidth)

    def __decl_ptr_var_with_lh(self, var_name, low, high, bitwidth):
        if var_name in self.env:
            raise Exception("Duplicate Declaration!!!")

        self.env[var_name] = PtrVal(low, high, bitwidth)

    # merge context of two branches
    def __merge(self, v, other):
        new_env = dict()
        for x in self.env:
            if x in other.env:
                v1 = self.env[x]
                v2 = other.env[x]
                if isinstance(v1, IntVal) and isinstance(v2, IntVal):
                    new_env[x] = IntVal(z3.If(v == 0, v2.val, v1.val),
                                        max(v1.bitwidth, v2.bitwidth))
                elif isinstance(v1, PtrVal) and isinstance(v2, PtrVal) and v1.bitwidth == v2.bitwidth:
                    new_env[x] = PtrVal(z3.If(v == 0, v2.low, v1.low),
                                        z3.If(v == 0, v2.high, v1.high),
                                        v1.bitwidth)
                else:
                    raise Exception("Merge Failed...")
        self.env = new_env
