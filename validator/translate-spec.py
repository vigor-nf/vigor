#!/usr/bin/python3
import ast
import sys
import os

protocolHeaders = {'ether' : ['saddr', 'daddr', 'type'],
                   'ipv4' : ['vihl', 'tos', 'len', 'pid', 'foff',
                             'ttl', 'npid', 'cksum', 'saddr', 'daddr'],
                   'tcpudp' : ['src_port', 'dst_port']}
emap = {'name' : 'emap',
        'modifying' : ['refresh_idx', 'add', 'expire_all', 'erase']}
vector = {'name' : 'vector',
          'modifying' : ['set']}
lpm = {'name' : 'lpm',
       'modifying' : []}
headerStack = 'recv_headers'
dummyCnt = 0
objects = {}
stateVars = []

indentLevel = 0
indentWidth = 2

importSearchDirs = []
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
    prefix = "rte_" if expr.func.id != 'tcpudp' else ""  
    result = prefix + expr.func.id + "_hdr(" + prefix + expr.func.id + "_hdrc("
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
    elif isinstance(expr, ast.Ellipsis):
        return '_'
    elif isinstance(expr, ast.Call):
        if isHeaderConstructor(expr):
            return renderHeaderConstructor(expr)
        if isinstance(expr.func, ast.Attribute):
            assert isinstance(expr.func.value, ast.Name)
            assert expr.func.value.id in stateObjects
            objMeta = stateObjects[expr.func.value.id]
            head = objMeta['name'] + '_' + expr.func.attr
            if expr.func.attr in objMeta['modifying']:
                head = expr.func.value.id + ' = ' + head
            args = ', '.join([expr.func.value.id] +
                             list(map(renderExpr, expr.args)))
        else:
            head = expr.func.id
            args = ', '.join(list(map(renderExpr, expr.args)))
        assert not expr.keywords, \
            "keywords are not recognized:" + ast.dump(expr)
        return "{}({})".format(head, args)
    elif isinstance(expr, ast.Compare):
        left = renderExpr(expr.left)
        assert len(expr.ops) == 1
        relation = expr.ops[0]
        assert len(expr.comparators) == 1
        right = renderExpr(expr.comparators[0])
        if   isinstance(relation, ast.Lt): sign = '<'
        elif isinstance(relation, ast.LtE): sign = '<='
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
        elif isinstance(expr.op, ast.Mult): sign = '*'
        elif isinstance(expr.op, ast.Div): sign = '/'
        elif isinstance(expr.op, ast.BitAnd): sign = '&'
        elif isinstance(expr.op, ast.BitOr): sign = '|'
        elif isinstance(expr.op, ast.LShift): sign = '<<'
        elif isinstance(expr.op, ast.RShift): sign = '>>'
        else: sign = '???'
        return "({} {} {})".format(left, sign, right)
    elif isinstance(expr, ast.BoolOp):
        left = renderExpr(expr.values[0])
        right = renderExpr(expr.values[1])
        if   isinstance(expr.op, ast.And): sign = ' && '
        elif isinstance(expr.op, ast.Or): sign = ' || '
        else: sign = '???'
        return "(" + (sign.join(map(renderExpr, expr.values))) + ")"
    elif isinstance(expr, ast.List):
        result = ""
        for e in reversed(expr.elts):
            result = "cons(" + renderExpr(e) + ", " + result
        return result + "nil" + (")" * len(expr.elts))
    elif isinstance(expr, ast.Attribute):
        assert isinstance(expr.value, ast.Name)
        assert expr.value.id in objects, \
            "object {} is not known".format(expr.value.id)
        assert expr.attr in objects[expr.value.id], \
            "object {} has no attribute {}".format(expr.value.id, expr.attr)
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
        return "assert sent_on_ports == {};\nassert sent_headers == {};".\
            format(renderExpr(ports), renderExpr(headers))
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
    prevHeaderStack = headerStack
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
    prefix = "rte_" if protocol != 'tcpudp' else ""
    assert protocol in protocolHeaders
    for p in protocolHeaders.keys():
        if p != protocol:
            pre = "rte_" if p != 'tcpudp' else ""
            indentPrint("case {}(dummy): {}".format(pre + p + '_hdr', onMismatch))
    obj = binding.targets[0].id
    fields = protocolHeaders[protocol]
    fieldInstances = list(map(lambda f : obj + '_' + f, fields))
    objects[obj] = dict(zip(fields, fieldInstances))
    hdrName = prefix + protocol + '_hdr_shell'
    indentPrint("case {}({}): switch({}) {{".\
                format(prefix + protocol + '_hdr', hdrName, hdrName))
    indentPrint("case {}({}): ".\
                format(prefix + protocol + '_hdrc', ", ".join(fieldInstances)))
    translate(body, declaredVars)
    headerStack = prevHeaderStack
    indentPrint("}}}")

def objConstructKey(call):
    return call.func.value.id + '.' + call.func.attr

def isObjAssignment(expr):
    if (not isinstance(expr, ast.Assign) or
        len(expr.targets) != 1):
        return False
    target = expr.targets[0]
    value = expr.value
    if (not isinstance(target, ast.Name) or
        not isinstance(value, ast.Call) or
        not isinstance(value.func, ast.Attribute) or
        not isinstance(value.func.value, ast.Name) or
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
    indentPrint("switch({}) {{ case {}({}):".\
                format(renderExpr(binding.value),
                       ctor, ", ".join(fieldInstances)))
    translate(body, declaredVars)
    indentPrint("}")

def endsWithReturn(exprList):
    for e in exprList:
        for ee in ast.walk(e):
            if isinstance(e, ast.Return):
                return True
    return False

def translate(exprList, declaredVars):
    global indentLevel, stateVars
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
                        indentPrint("{} {} = {};".\
                                    format(guessType(expr.value),
                                           target.id, value))
            else:
                indentPrint("Weird assignment")
        elif isinstance(expr, ast.If):
            indentPrint("if ({}) {{".format(renderExpr(expr.test)))
            translate(expr.body, declaredVars.copy())
            if expr.orelse:
                indentPrint("} else {")
                translate(expr.orelse, declaredVars.copy())
                indentPrint("}")
            elif endsWithReturn(expr.body):
                indentPrint("} else {")
                translate(exprList, declaredVars.copy())
                indentPrint("}")
                break
            else:
                indentPrint("}")
        elif isinstance(expr, ast.Assert):
            indentPrint("assert {};".format(renderExpr(expr.test)))
        elif isinstance(expr, ast.Return):
            indentPrint(genOutcome(expr.value))
        elif isinstance(expr, ast.Expr):
            indentPrint(renderExpr(expr.value) + ';')
        elif isinstance(expr, ast.Pass):
            indentPrint('assume(false); //Ignore this case')
        elif isinstance(expr, ast.Import):
            for alias in expr.names:
                assert alias.asname == None
                found = False
                for d in importSearchDirs:
                    path = os.path.join(d, 'paygo-' + alias.name + '.py')
                    if os.path.isfile(path):
                        translateSpec(path)
                        found = True
                        break
                assert found, alias.name + ' file not found'
        elif isinstance(expr, ast.ImportFrom):
            assert expr.module == 'state'
            for alias in expr.names:
                assert alias.asname == None
                assert alias.name in stateObjects
                stateVars.append(alias.name)
                declaredVars.append(alias.name)
        else:
            indentPrint ("Unrecognized construct {}".format(ast.dump(expr)))
    indentLevel -= 1

pythonSpecFname = sys.argv[1]
vfSpecFname = sys.argv[2]
nfFolder = sys.argv[3]
importSearchDirs.append(nfFolder)
customPreamble = ''
#FIXME: this code should be autogenerated from the */dataspec.ml files
exec(open(nfFolder + '/dataspec.py').read())
def translateSpec(pythonSpecFname_):
    global importSearchDirs
    specRaw = open(pythonSpecFname_).read()
    specAst = ast.parse(specRaw)
    importSearchDirs.append(os.path.split(pythonSpecFname_)[0])
    return translate(specAst.body, [])

vfSpecFile = open(vfSpecFname, "w")
indentPrint("bit_and_hack();")
indentPrint(customPreamble)
translateSpec(pythonSpecFname)
for v in stateVars:
    indentPrint("assert final_{} == {};".format(v, v))
vfSpecFile.close()
