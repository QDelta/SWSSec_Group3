from pycparser import c_ast, c_parser
from asthelper import *

text = r"""
int get(int *arr, int n, int head) {
    ASSUME(n > 0, capacity(arr) >= n * sizeof(int));
    if (head) {
        return arr[0];
    } else {
        return arr[n];
    }
}
"""

if __name__ == '__main__':
    parser = c_parser.CParser()
    ast: c_ast.FileAST = parser.parse(text)

    fundef: c_ast.FuncDef = ast.ext[0]

    params, assumes, body = split_fundef(fundef)
    print(params)
    for a in assumes:
        a.show()
    body.show()

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