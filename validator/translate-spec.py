#!/usr/bin/python3
import ast

protocolHeaders = {'ether' : ['saddr', 'daddr', 'type'],
                   'ipv4' : ['vihl', 'tos', 'len', 'pid', 'foff',
                             'ttl', 'npid', 'cksum', 'saddr', 'daddr'],
                   'tcpudp' : ['src_port', 'dst_port'],
                   'tcp' : ['srcp', 'dstp', 'seq', 'ack', 'doff',
                            'flags', 'win', 'cksum', 'urp']}
objConstructors = {'emap_get_key' : {'constructor' : 'FlowIdc',
                                     'type' : 'FlowIdi',
                                     'fields' : ['sp', 'dp', 'sip', 'dip', 'idev', 'prot']}}
typeConstructors = {'FlowIdc' : 'FlowIdi',
                    'emap' : 'emap<FlowIdi>'}
headerStack = 'recv_headers'
dummyCnt = 0
objects = {}
stateVars = ['flow_emap']
declaredVars = stateVars.copy()

indentLevel = 0
indentWidth = 2

specFile = None

def indentPrint(text):
    specFile.write(' '*indentLevel*indentWidth + text + '\n')

def guessType(rhs):
    if (isinstance(rhs, ast.Call) and
        isinstance(rhs.func, ast.Name) and
        rhs.func.id in typeConstructors):
        return typeConstructors[rhs.func.id]
    return "int"

def isHeaderConstructor(expr):
    return (isinstance(expr, ast.Call) and
            isinstance(expr.func, ast.Name) and
            expr.func.id in protocolHeaders)

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
    setFields = dict(map(lambda kw : (kw.arg, kw.value), expr.keywords))
    result = expr.func.id + "_hdr(" + expr.func.id + "_hdrc("
    first = True
    for f in protocolHeaders[expr.func.id]:
        if first:
            first = False
        else:
            result += ', '
        if f in setFields:
            if isinstance(setFields[f], ast.Ellipsis):
                result += '_'
            else:
                result += renderExpr(setFields[f])
        else:
            assert base != None, expr.func.id + " undefined field " + f
            result += base[f]
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
        if   isinstance(relation, ast.LtE): sign = '<='
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
        for e in reversed(expr.elts):
            result = "cons(" + renderExpr(e) + ", " + result
        return result + "nil" + (")" * len(expr.elts))
    elif isinstance(expr, ast.Attribute):
        assert isinstance(expr.value, ast.Name)
        assert expr.value.id in objects, "object {} is not known".format(expr.value.id)
        assert expr.attr in objects[expr.value.id], "object {} has no attribute {}".format(expr.value.id, expr.attr)
        return objects[expr.value.id][expr.attr]
    else:
        return "complicated"

def genOutcome(portsHeaders):
    assert isinstance(portsHeaders, ast.Tuple)
    assert len(portsHeaders.elts) == 2
    ports = portsHeaders.elts[0]
    headers = portsHeaders.elts[1]
    assert isinstance(ports, ast.List)
    assert isinstance(headers, ast.List)
    if ports.elts:
        return "assert sent_on_ports == {}; assert sent_headers == {};".format(renderExpr(ports), renderExpr(headers))
    else:
        return "assert sent_on_ports == nil;"

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

def translatePopHeader(binding, body):
    global headerStack, dummyCnt, objects
    indentPrint("switch({}) {{\n".format(headerStack))
    onMismatch = genOutcome(binding.value.keywords[0].value)
    indentPrint("case nil: {}".format(onMismatch))
    headerStackTail = headerStack + "_t"
    header = "tmp" + str(dummyCnt)
    dummyCnt += 1
    indentPrint("case cons({}, {}):".format(header, headerStackTail))
    headerStack = headerStackTail
    indentPrint("switch({}) {{".format(header))
    protocol = binding.value.args[0].id
    assert protocol in protocolHeaders
    for p in protocolHeaders.keys():
        if p != protocol:
            indentPrint("case {}(dummy): {}".format(p + '_hdr', onMismatch))
    obj = binding.targets[0].id
    fields = protocolHeaders[protocol]
    fieldInstances = list(map(lambda f : obj + '_' + f, fields))
    objects[obj] = dict(zip(fields, fieldInstances))
    hdrName = protocol + '_hdr_shell'
    indentPrint("case {}({}): switch({}) {{".format(protocol + '_hdr', hdrName, hdrName))
    indentPrint("case {}({}): ".format(protocol + '_hdrc', ", ".join(fieldInstances)))
    translate(body)
    indentPrint("}}}")

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
    varName = binding.targets[0].id
    fields = objConstructors[binding.value.func.id]['fields']
    ctor = objConstructors[binding.value.func.id]['constructor']
    fieldInstances = list(map(lambda f : varName + '_' + f, fields))
    objects[varName] = dict(zip(fields, fieldInstances))
    indentPrint("switch({}) {{ case {}({}):".format(renderExpr(binding.value), ctor, ", ".join(fieldInstances)))
    translate(body)
    indentPrint("}")

def translate(exprList):
    global indentLevel
    indentLevel += 1
    while exprList:
        [expr, *exprList] = exprList
        if isinstance(expr, ast.Assign):
            assert isinstance(expr.targets, list)
            target = expr.targets[0]
            if isinstance(target, ast.Name):
                if isPopHeader(expr):
                    translatePopHeader(expr, exprList)
                    break
                if isObjAssignment(expr):
                    translateObjAssignment(expr, exprList)
                    break
                assert len(expr.targets) == 1
                value = renderExpr(expr.value)
                if target.id.isupper():
                    indentPrint("#define {} ({})".format(target.id, value))
                else:
                    global declaredVars
                    if target.id in declaredVars:
                        indentPrint("{} = {};".format(target.id, value))
                    else:
                        declaredVars.append(target.id)
                        indentPrint("{} {} = {};".format(guessType(expr.value), target.id, value))
            else:
                indentPrint("Weird assignment")
        elif isinstance(expr, ast.If):
            indentPrint("if ({}) {{".format(renderExpr(expr.test)))
            translate(expr.body)
            indentPrint("} else {")
            translate(expr.orelse)
            indentPrint("}")
        elif isinstance(expr, ast.Assert):
            indentPrint("assert {};".format(renderExpr(expr.test)))
        elif isinstance(expr, ast.Return):
            indentPrint(genOutcome(expr.value))
        else:
            indentPrint ("Unrecognized construct {}".format(ast.dump(expr)))
    indentLevel -= 1

specRaw = open("nat_spec.py").read()
specAst = ast.parse(specRaw)
specFile = open("forwarding_property.tmpl", "w")
indentPrint("bit_and_hack();")
translate(specAst.body)
for v in stateVars:
    indentPrint("assert final_{} == {};".format(v, v))
specFile.close()
