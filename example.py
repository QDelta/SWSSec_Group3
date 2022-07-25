from pycparser import c_ast, c_parser
from asthelper import *
from symexec import ExecContext

text = r"""
int get(int *arr, int n, int head) {
    ASSUME(-n < 0, +n > 0, capacity(arr) >= n * sizeof(int));
    if (head) {
        return arr[0];
    } else {
        return arr[n];
    }
}
"""

test_text0 = r"""
int get(int *arr, int n, int head) {
    ASSUME(-n < 0, +n > 0, capacity(arr) == n * sizeof(int));


    char var_char1 = 'A';
    char var_char2;

    int var_name1 = 100;
    int var_name2 = var_name1 * 2;
    int *var_arary1;
    int *var_arary2 = arr;
    var_name1 = var_name2 - 10;
    var_name2 = - var_name2;
    
    var_name1 = arr[0];
    var_name2 = arr[1];
}
"""

test_text1 = r"""
int get(int *arr, int n, int head) {
    ASSUME(-n < 0, +n > 0, capacity(arr) == n * sizeof(int));
    
    if (head) {
        return arr[0];
    } else {
        return arr[n];
    }
    
    char var_char1 = 'A';
    char var_char2;
    
    int var_name1 = 100;
    int var_name2 = var_name1 * 2;
    int *var_arary1;
    int *var_arary2 = arr;
    var_name1 = var_name2 - 10;
    var_name2 = - var_name2;
}
"""

test_text2 = r"""
#include <stdio.h>

int get(int *arr, int n, int head, char testChar1, char *testChar2) {
    ASSUME(-n < 0, +n > 0, testChar1 > 36, capacity(arr) >= n * sizeof(int));
    // test-comment1
    if (head) {
        // test-comment2
        return arr[0];
        /*
            test-multiline-comment1 
        */
    } else {
    // test-comment3
        return arr[n];
        // test-comment4
    }
    // test-comment5
}
"""

if __name__ == '__main__':
    # * Parser Part * #
    # C Code Cleaning: #include and comment.
    pass

    # Parse C code into abstract symbolic tree.
    parser = c_parser.CParser()
    ast: c_ast.FileAST = parser.parse(test_text0)
    fundef: c_ast.FuncDef = ast.ext[0]  # Assumption: the input of C code only has one function.

    # Debugging:
    params, assumes, body = split_fundef(fundef)  # Divide C code function into three parts.
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

    exe = ExecContext(params, assumes, body)
    # Before execution, the E and P:
    exe.print_env()
    exe.print_path_cond()
    exe.run()
    # After execution, the E and P:
    exe.print_env()
    exe.print_path_cond()
    # Run path condition checking.
    exe.check()

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
    #
