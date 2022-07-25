from pycparser import c_parser
from asthelper import *
from symexec import ExecContext
import z3

def analyze(code):
    parser = c_parser.CParser()
    ast = parser.parse(code)
    fundef = ast.ext[0]
    params, assumes, body = split_fundef(fundef)

    ctx = ExecContext(params, assumes)
    counter_examples = ctx.exec(body)

    error_lines = []
    error_models = []

    for formula, lineno in counter_examples:
        s = z3.Solver()
        result = s.check(formula)
        if result == z3.sat:
            error_lines.append(lineno)
            error_models.append(s.model())

    return error_lines, error_models

text = r"""
void get(int *arr, int n, int head) {
    ASSUME(n > 0, capacity(arr) >= n);
    if (head == 0) {
        print(arr[0]);
    } else {
        print(arr[n]);
    }
}
"""

if __name__ == '__main__':
    # * Parser Part * #
    # C Code Cleaning: #include and comment.

    print(analyze(text))
    
    # print('[1]The params:')
    # print(params)
    #
    # print('[2]The assumes:')
    # for a in assumes:
    #     a.show()
    #
    # print('[3]The body:')
    # body.show()
    # print('*******************************')

    # print(params)
    # print(assumes)

    # exe = ExecContext(params, assumes, body)
    # # Before execution, the E and P:
    # exe.print_env()
    # exe.print_path_cond()
    # exe.run()
    # # After execution, the E and P:
    # exe.print_env()
    # exe.print_path_cond()
    # # Run path condition checking.
    # exe.check()

    # * SMT Solver, z3 Part * #
    # z3 example
    # import z3
    # a = z3.BitVec('a', 32)
    # b = z3.BitVec('b', 32)
    # s = z3.Solver()
    # s.add(z3.And(a <= b, a >= b, a + 1 >= 10))
    # result = s.check()
    # if result == z3.sat:
    #     print(s.model())
    # else:
    #     print(result)

    # Example: how to use ExecContext in symexec.py
    # exe = ExecContext(params, assumes, body)
    # exe.check()
