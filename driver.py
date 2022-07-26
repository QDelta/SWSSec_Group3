from pycparser import c_ast, c_parser
from asthelper import split_fundef
from symexec import ExecContext, SymExecError
import z3

TEST_SRC = r"""
void foo(int n) {
    int *arr;
    if (n > 0) {
        arr = alloc(n);
    }
    print(arr[0]);
}

void get(int *arr, int n, int head) {
    ASSUME(n > 0, capacity(arr) >= n);
    if (head != 0) {
        print(arr[0]);
    } else {
        print(arr[n]);
    }
}
"""

def get_fundefs(code_text):
    parser = c_parser.CParser()
    ast: c_ast.FileAST = parser.parse(code_text)
    fundefs = []
    for ext in ast.ext:
        if isinstance(ext, c_ast.FuncDef):
            fundefs.append(ext)
    return fundefs

def analyze_fundef(fundef):
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

def analyze(code_text):
    fundefs = get_fundefs(code_text)
    error_lines = []
    error_models = []
    for linenos, models in map(analyze_fundef, fundefs):
        error_lines += linenos
        error_models += models

    return error_lines, error_models

if __name__ == '__main__':
    # * Parser Part * #
    # C Code Cleaning: #include and comment.

    try:
        print(analyze(TEST_SRC))
    except SymExecError as e:
        print(f'[error] {e.msg}')
