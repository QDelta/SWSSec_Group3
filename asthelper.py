import pycparser.c_ast as csyn

# integer type: ('int', bitwidth)
# pointer type: ('ptr', bitwidth of element)

def bitwidth_of(c_type):
    if isinstance(c_type, csyn.IdentifierType):
        if c_type.names == ['int']:
            return 32
        elif c_type.names == ['char']:
            return 8

    raise Exception("unknown type ", c_type)

def decl_to_type(decl):
    if isinstance(decl, csyn.TypeDecl):
        return ('int', bitwidth_of(decl.type))
    elif isinstance(decl, csyn.PtrDecl):
        ty_kind, width = decl_to_type(decl.type)
        if ty_kind == 'int':
            return ('ptr', width)
        else: # ty_kind == 'ptr'
            return ('ptr', 64)

    raise Exception("unknown decl ", decl)

# ParamList -> (name, type) list
def extract_params(c_params: csyn.ParamList):
    c_params = c_params.params
    params = []
    for decl in c_params:
        params.append((decl.name, decl_to_type(decl.type)))
    return params

# FuncDef -> (name, type) list, assume (expr) list, body (stmt)
def split_fundef(fundef: csyn.FuncDef):
    c_params = fundef.decl.type.args
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