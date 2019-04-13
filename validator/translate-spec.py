#!/usr/bin/python3
import ast

specRaw = open("nat_spec.py").read()
specAst = ast.parse(specRaw)

def render_expr(expr):
    if isinstance(expr, ast.Name):
        return expr.id
    elif isinstance(expr, ast.Num):
        return expr.n
    elif isinstance(expr, ast.Call):
        args = ", ".join(list(map(render_expr, expr.args)))
        return "{}({})".format(expr.func.id, args)
    else:
        return "complicated"

def translate(exprList):
    for expr in exprList:
        if isinstance(expr, ast.Assign):
            value = render_expr(expr.value)
            assert isinstance(expr.targets, list)
            target = expr.targets[0]
            if isinstance(target, ast.Name):
                assert len(expr.targets) == 1
                if target.id.isupper():
                    print("#define {} ({})".format(target.id, value))
                else:
                    print("{} = {};".format(target.id, value))
            elif isinstance(target, ast.List):
                assert len(target.elts) == 2
                assert isinstance(target.elts[1], ast.Starred)
                print("list destructuring")
        elif isinstance(expr, ast.If):
            print("if ({}) {{".format(render_expr(expr.test)))
            translate(expr.body)
            print("} else {")
            translate(expr.orelse)
            print("}")
        elif isinstance(expr, ast.Assert):
            print("assert {};".format(render_expr(expr.test)))
        else:
            print ("Unrecognized construct {}".format(ast.dump(expr)))

translate(specAst.body)
