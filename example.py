from pycparser import c_parser, c_ast
import z3

text = r"""
int get(int *arr, int n) {
    ASSUME(capacity(arr) >= n * sizeof(int));
    return arr[n];
}
"""

if __name__ == '__main__':
    # pycparser example
    parser = c_parser.CParser()
    ast: c_ast.FileAST = parser.parse(text)
    ast.show()

    # z3 example
    a = z3.BitVec('a', 32)
    b = z3.BitVec('b', 32)
    s = z3.Solver()
    s.add(z3.And(a <= b, a >= b, a + 1 >= 10))
    result = s.check()
    if result == z3.sat:
        print(s.model())
    else:
        print(result)