#!/usr/bin/python3
import ast

specRaw = open("nat_spec.py").read()
specAst = ast.parse(specRaw)

def isHeaderConstructor(expr):
    return (isinstance(expr, ast.Call) and
            isinstance(expr.func, ast.Name) and
            expr.func.id in protocol_headers)

def renderHeaderConstructor(expr):
    protocol = expr.func.id
    if expr.args:
        assert len(expr.args) == 1
        assert isinstance(expr.args[0], ast.Name)
        base = expr.args[0].id
        assert base in objects
        base = objects[base]
    else:
        base = None
    set_fields = dict(map(lambda kw : (kw.arg, kw.value), expr.keywords))
    result = expr.func.id + "_hdr(" + expr.func.id + "_hdrc("
    for f in protocol_headers[expr.func.id]:
        if f in set_fields:
            if isinstance(set_fields[f], ast.Ellipsis):
                result += '_'
            else:
                result += renderExpr(set_fields[f])
        else:
            assert base != None, expr.func.id + " undefined field " + f
            result += base[f]
        result += ", "
    result += "))"
    return result

def renderExpr(expr):
    if isinstance(expr, ast.Name):
        return expr.id
    elif isinstance(expr, ast.Num):
        return expr.n
    elif isinstance(expr, ast.Call):
        if isHeaderConstructor(expr):
            return renderHeaderConstructor(expr)
        assert not expr.keywords, "keywords are not recognized:" + ast.dump(expr)
        args = ", ".join(list(map(renderExpr, expr.args)))
        return "{}({})".format(expr.func.id, args)
    elif isinstance(expr, ast.Compare):
        left = renderExpr(expr.left)
        assert len(expr.ops) == 1
        relation = expr.ops[0]
        assert len(expr.comparators) == 1
        right = renderExpr(expr.comparators[0])
        if   isinstance(relation, ast.Lt): sign = '<'
        elif isinstance(relation, ast.Eq): sign = '=='
        elif isinstance(relation, ast.NotEq): sign = '!='
        elif isinstance(relation, ast.Gt): sign = '>'
        else: sign = '???'
        return "({} {} {})".format(left, sign, right)
    elif isinstance(expr, ast.BinOp):
        left = renderExpr(expr.left)
        right = renderExpr(expr.right)
        if   isinstance(expr.op, ast.Sub): sign = '-'
        elif isinstance(expr.op, ast.Add): sign = '+'
        elif isinstance(expr.op, ast.BitAnd): sign = '&'
        else: sign = '???'
        return "({} {} {})".format(left, sign, right)
    elif isinstance(expr, ast.BoolOp):
        left = renderExpr(expr.values[0])
        right = renderExpr(expr.values[1])
        if   isinstance(expr.op, ast.And): sign = '&&'
        elif isinstance(expr.op, ast.Or): sign = '||'
        else: sign = '???'
        return "(" + (sign.join(map(renderExpr, expr.values))) + ")"
    elif isinstance(expr, ast.List):
        result = ""
        for e in expr.elts:
            result = "cons(" + renderExpr(e) + ", " + result
        return result + "nil" + (")" * len(expr.elts))
    elif isinstance(expr, ast.Attribute):
        assert isinstance(expr.value, ast.Name)
        assert expr.value.id in objects, "object {} is not known".format(expr.value.id)
        assert expr.attr in objects[expr.value.id], "object {} has no attribute {}".format(expr.value.id, expr.attr)
        return objects[expr.value.id][expr.attr]
    else:
        return "complicated"

def genOutcome(ports_headers):
    assert isinstance(ports_headers, ast.Tuple)
    assert len(ports_headers.elts) == 2
    ports = ports_headers.elts[0]
    headers = ports_headers.elts[1]
    assert isinstance(ports, ast.List)
    assert isinstance(headers, ast.List)
    if ports.elts:
        return "assert sent_on_ports == {} && sent_headers == {};".format(renderExpr(ports), renderExpr(headers))
    else:
        return "assert sent_on_ports == [];"

def isPopHeader(expr):
    if (not isinstance(expr, ast.Assign) or
        len(expr.targets) != 1):
        return False
    target = expr.targets[0]
    value = expr.value
    if (not isinstance(target, ast.Name) or
        not isinstance(value, ast.Call) or
        not isinstance(value.func, ast.Name) or
        value.func.id != 'pop_header'):
        return False
    assert len(value.keywords) == 1
    assert value.keywords[0].arg == 'on_mismatch'
    assert len(value.args) == 1
    assert isinstance(value.args[0], ast.Name)
    return True

protocol_headers = {'ether':['saddr', 'daddr', 'type'],
                    'ipv4':['vihl', 'tos', 'len', 'pid', 'foff',
                            'ttl', 'pid', 'cksu', 'saddr', 'daddr'],
                    'tcpudp':['src_port', 'dst_port']}
header_stack = "recv_headers"
dummy_cnt = 0
objects = {}
def translatePopHeader(binding, body):
    global header_stack, dummy_cnt, objects
    print("switch({}) {{\n".format(header_stack))
    on_mismatch = genOutcome(binding.value.keywords[0].value)
    print("case nil: {}".format(on_mismatch))
    header_stack_tail = header_stack + "_t"
    header = "tmp" + str(dummy_cnt)
    dummy_cnt += 1
    print("case cons({}, {}):".format(header, header_stack_tail))
    header_stack = header_stack_tail
    print("switch({}) {{".format(header))
    protocol = binding.value.args[0].id
    assert protocol in protocol_headers
    for p in protocol_headers.keys():
        if p != protocol:
            print("case {}(dummy): {}".format(p + '_hdr', on_mismatch))
    obj = binding.targets[0].id
    fields = protocol_headers[protocol]
    field_instances = list(map(lambda f : obj + '_' + f, fields))
    objects[obj] = dict(zip(fields, field_instances))
    hdr_name = protocol + '_hdr_shell'
    print("case {}({}): switch({}) {{".format(protocol + '_hdr', hdr_name, hdr_name))
    print("case {}({}): ".format(protocol + '_hdrc', ", ".join(field_instances)))
    translate(body)
    print("}}}")

objConstructors = {'emap_get_key':{'constructor' : 'FlowIdc',
                                   'fields' : ['sp', 'dp', 'sip', 'dip', 'idev', 'prot']}}
def isObjAssignment(expr):
    if (not isinstance(expr, ast.Assign) or
        len(expr.targets) != 1):
        return False
    target = expr.targets[0]
    value = expr.value
    if (not isinstance(target, ast.Name) or
        not isinstance(value, ast.Call) or
        not isinstance(value.func, ast.Name) or
        value.func.id not in objConstructors):
        return False
    return True

def translateObjAssignment(binding, body):
    global objects
    var_name = binding.targets[0].id
    fields = objConstructors[binding.value.func.id]['fields']
    ctor = objConstructors[binding.value.func.id]['constructor']
    field_instances = list(map(lambda f : var_name + '_' + f, fields))
    objects[var_name] = dict(zip(fields, field_instances))
    print("switch({}) {{ case {}({}):".format(renderExpr(binding.value), ctor, ", ".join(field_instances)))
    translate(body)
    print("}")

def translate(exprList):
    while exprList:
        [expr, *exprList] = exprList
        if isinstance(expr, ast.Assign):
            assert isinstance(expr.targets, list)
            target = expr.targets[0]
            if isinstance(target, ast.Name):
                if isPopHeader(expr):
                    translatePopHeader(expr, exprList)
                    return
                if isObjAssignment(expr):
                    translateObjAssignment(expr, exprList)
                    return
                assert len(expr.targets) == 1
                value = renderExpr(expr.value)
                if target.id.isupper():
                    print("#define {} ({})".format(target.id, value))
                else:
                    print("{} = {};".format(target.id, value))
            else:
                print("Weird assignment")
        elif isinstance(expr, ast.If):
            print("if ({}) {{".format(renderExpr(expr.test)))
            translate(expr.body)
            print("} else {")
            translate(expr.orelse)
            print("}")
        elif isinstance(expr, ast.Assert):
            print("assert {};".format(renderExpr(expr.test)))
        elif isinstance(expr, ast.Return):
            print(genOutcome(expr.value))
        else:
            print ("Unrecognized construct {}".format(ast.dump(expr)))

translate(specAst.body)
