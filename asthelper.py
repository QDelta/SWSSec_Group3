import pycparser.c_ast as csyn

# int   : 'int'
# int * : 'intptr'

def decl_to_type(decl):
    if isinstance(decl, csyn.TypeDecl):
        return 'int'
    elif isinstance(decl, csyn.PtrDecl):
        return 'ptr'

    raise Exception("unknown decl ", decl)

# ParamList -> (name, type) list
def extract_params(c_params: csyn.ParamList) -> list:
    c_params = c_params.params
    params = []
    for decl in c_params:
        params.append((decl.name, decl_to_type(decl.type)))
    return params

# FuncDef -> params (name, type, bitwidth) list, assume (expr) list, body (stmt)
def split_fundef(fundef: csyn.FuncDef):
    c_params: csyn.ParamList = fundef.decl.type.args
    params = extract_params(c_params)

    body: csyn.Compound = fundef.body

    assumes = []
    if len(body.block_items) > 0:
        maybe_assume = body.block_items[0]
        if isinstance(maybe_assume, csyn.FuncCall):
            if isinstance(maybe_assume.name, csyn.ID):
                if maybe_assume.name.name == 'ASSUME':
                    assumes = maybe_assume.args.exprs
                    body.block_items = body.block_items[1:]

    return params, assumes, body
