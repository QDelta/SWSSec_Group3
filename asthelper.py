from pycparser import c_ast

# int   : 'int'
# int * : 'intptr'

def decl_to_type(decl):
    if isinstance(decl, c_ast.TypeDecl):
        return 'int'
    elif isinstance(decl, c_ast.PtrDecl):
        return 'ptr'

    raise Exception("unknown decl ", decl)

# ParamList -> (name, type) list
def extract_params(c_params: c_ast.ParamList) -> list:
    c_params = c_params.params
    params = []
    for decl in c_params:
        params.append((decl.name, decl_to_type(decl.type)))
    return params

# FuncDef -> params (name, type, bitwidth) list, assume (expr) list, body (stmt)
def split_fundef(fundef: c_ast.FuncDef):
    c_params: c_ast.ParamList = fundef.decl.type.args
    params = extract_params(c_params)

    body: c_ast.Compound = fundef.body

    assumes = []
    if len(body.block_items) > 0:
        maybe_assume = body.block_items[0]
        if isinstance(maybe_assume, c_ast.FuncCall):
            if isinstance(maybe_assume.name, c_ast.ID):
                if maybe_assume.name.name == 'ASSUME':
                    assumes = maybe_assume.args.exprs
                    body.block_items = body.block_items[1:]

    return params, assumes, body
