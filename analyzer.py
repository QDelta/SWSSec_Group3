from pycparser import c_ast, c_parser
from asthelper import *
from symexec import ExecContext


class ProgramAnalyzer:
    def __init__(self, code: str):
        self.__parser = c_parser.CParser()
        self.__code = code
        self.__ast = None
        self.__exe = None
        self.__clean()
        self.__parse()

    def __clean(self):
        pass

    def __parse(self):
        self.__ast = self.__parser.parse(self.__code)

    def run(self):
        fundefs = []
        for fundef in self.__ast:
            fundefs.append([split_fundef(fundef)])

        for fundef in fundefs:
            self.__exe = ExecContext(*fundef)
            self.__exe.run()
            self.__exe.check()


input_c_code = r"""
int get(int *arr, int n, int head) {
    ASSUME(-n < 0, +n > 0, capacity(arr) == n * sizeof(int));
    
    int var_name1 = 100;
    int var_name2 = var_name1 * 2;
    int *var_arary1;
    int *var_arary2 = arr;
    char var_char1 = 'A';
    char var_char2;
    var_name1 = var_name2 - 10;
    var_name2 = - var_name2;
    
    if (head) {
        return arr[0];
    } else {
        return arr[n];
    }
}
"""

# How to use Program Analyzer.
if __name__ == '__main__':
    ProgramAnalyzer(input_c_code).run()
