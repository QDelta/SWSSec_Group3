from pycparser import c_parser
from asthelper import *
from symexec import ExecContext, SymExecError
import z3

TEST_SRC = r"""
void get(int *arr, int n, int head) {
    ASSUME(n > 0, capacity(arr) >= n);
    if (head == 0) {
        print(arr[0]);
    } else {
        print(arr[n]);
    }
}
"""

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
        elif result == z3.unknown:
            raise SymExecError(f"Can not solve line {lineno}")

    return error_lines, error_models

if __name__ == '__main__':
    # * Parser Part * #
    # C Code Cleaning: #include and comment.

    try:
        print(analyze(TEST_SRC))
    except SymExecError as e:
        print(f'[error] {e.msg}')
