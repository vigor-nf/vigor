#!/usr/bin/python3
import ast
import sys

protocolHeaders = {'ether' : ['saddr', 'daddr', 'type'],
                   'ipv4' : ['vihl', 'tos', 'len', 'pid', 'foff',
                             'ttl', 'npid', 'cksum', 'saddr', 'daddr'],
                   'tcpudp' : ['src_port', 'dst_port'],
                   'tcp' : ['srcp', 'dstp', 'seq', 'ack', 'doff',
                            'flags', 'win', 'cksum', 'urp']}
objConstructors = {'emap_get_key|flow_emap' : {'constructor' : 'FlowIdc',
                                               'type' : 'FlowIdi',
                                               'fields' : ['sp', 'dp', 'sip', 'dip', 'idev', 'prot']}}
typeConstructors = {'FlowIdc' : 'FlowIdi',
                    'emap' : 'emap<FlowIdi>'}
headerStack = 'recv_headers'
dummyCnt = 0
objects = {}
stateVars = ['flow_emap']

indentLevel = 0
indentWidth = 2

vfSpecFile = None

def indentPrint(text):
    vfSpecFile.write(' '*indentLevel*indentWidth + text + '\n')

def guessType(rhs):
    if (isinstance(rhs, ast.Call) and
        isinstance(rhs.func, ast.Name) and
        rhs.func.id in typeConstructors):
        return typeConstructors[rhs.func.id]
    elif (isinstance(rhs, ast.NameConstant) and
          (rhs.value == True or rhs.value == False)):
        return "bool"
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
    for f in setFields.keys():
        assert f in protocolHeaders[expr.func.id]
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
    elif isinstance(expr, ast.UnaryOp):
        if isinstance(expr.op, ast.USub):
            return '-' + str(renderExpr(expr.operand))
        else:
            assert isinstance(expr.op, ast.Not)
            return '!' + renderExpr(expr.operand)
    elif isinstance(expr, ast.NameConstant):
        if expr.value == True:
            return str('true')
        elif expr.value == False:
            return str('false')
        else:
            return "unknown named constant" + expr.value
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

def translatePopHeader(binding, body, declaredVars):
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
    translate(body, declaredVars)
    indentPrint("}}}")

def objConstructKey(call):
    return call.func.id + '|' + call.args[0].id

def isObjAssignment(expr):
    if (not isinstance(expr, ast.Assign) or
        len(expr.targets) != 1):
        return False
    target = expr.targets[0]
    value = expr.value
    if (not isinstance(target, ast.Name) or
        not isinstance(value, ast.Call) or
        not isinstance(value.func, ast.Name) or
        not value.args or
        not isinstance(value.args[0], ast.Name) or
        objConstructKey(value) not in objConstructors):
        return False
    return True

def translateObjAssignment(binding, body, declaredVars):
    global objects
    varName = binding.targets[0].id
    fields = objConstructors[objConstructKey(binding.value)]['fields']
    ctor = objConstructors[objConstructKey(binding.value)]['constructor']
    fieldInstances = list(map(lambda f : varName + '_' + f, fields))
    objects[varName] = dict(zip(fields, fieldInstances))
    indentPrint("switch({}) {{ case {}({}):".format(renderExpr(binding.value), ctor, ", ".join(fieldInstances)))
    translate(body, declaredVars)
    indentPrint("}")

def translate(exprList, declaredVars):
    global indentLevel
    indentLevel += 1
    while exprList:
        [expr, *exprList] = exprList
        if isinstance(expr, ast.Assign):
            assert isinstance(expr.targets, list)
            target = expr.targets[0]
            if isinstance(target, ast.Name):
                if isPopHeader(expr):
                    translatePopHeader(expr, exprList, declaredVars.copy())
                    break
                if isObjAssignment(expr):
                    translateObjAssignment(expr, exprList, declaredVars.copy())
                    break
                assert len(expr.targets) == 1
                value = renderExpr(expr.value)
                if target.id.isupper():
                    indentPrint("#define {} ({})".format(target.id, value))
                else:
                    if target.id in declaredVars:
                        indentPrint("{} = {};".format(target.id, value))
                    else:
                        declaredVars.append(target.id)
                        indentPrint("{} {} = {};".format(guessType(expr.value), target.id, value))
            else:
                indentPrint("Weird assignment")
        elif isinstance(expr, ast.If):
            indentPrint("if ({}) {{".format(renderExpr(expr.test)))
            translate(expr.body, declaredVars.copy())
            indentPrint("} else {")
            translate(expr.orelse, declaredVars.copy())
            indentPrint("}")
        elif isinstance(expr, ast.Assert):
            indentPrint("assert {};".format(renderExpr(expr.test)))
        elif isinstance(expr, ast.Return):
            indentPrint(genOutcome(expr.value))
        else:
            indentPrint ("Unrecognized construct {}".format(ast.dump(expr)))
    indentLevel -= 1

pythonSpecFname = sys.argv[1]
vfSpecFname = sys.argv[2]
specRaw = open(pythonSpecFname).read()
specAst = ast.parse(specRaw)
vfSpecFile = open(vfSpecFname, "w")
indentPrint("bit_and_hack();")

globalVars = stateVars.copy()
#FIXME: this code should be autogenerated from the */data_spec.ml files
if 'bridge' in pythonSpecFname:
    objConstructors = {'vector_get|dyn_vals' : {'constructor' : 'DynamicValuec',
                                                'type' : 'DynamicValuei',
                                                'fields' : ['output_port']}}
    typeConstructors = {'StaticKeyc' : 'StaticKeyi'}
    stateVars = ['dyn_emap', 'dyn_vals']
    indentPrint("dchain stat_chain; //dummy")
    indentPrint("emap<StaticKeyi> stat_emap = emap(initial_st_map, initial_st_vec, stat_chain);")
    globalVars = stateVars.copy()
    globalVars.append('stat_emap')
elif 'lb' in pythonSpecFname:
    objConstructors = {'vector_get|backends' : {'constructor' : 'LoadBalancedBackendc',
                                                'type' : 'LoadBalancedBackendi',
                                                'fields' : ['nic', 'mac', 'ip']}}
    typeConstructors = {'ip_addrc' : 'ip_addri',
                        'LoadBalancedFlowc' : 'LoadBalancedFlowi'}
    stateVars = ['flow_emap', 'flow_id_to_backend_id', 'backends', 'backend_ip_emap', 'cht']
    globalVars = stateVars.copy()
    globalVars


translate(specAst.body, globalVars)
for v in stateVars:
    indentPrint("assert final_{} == {};".format(v, v))
vfSpecFile.close()
