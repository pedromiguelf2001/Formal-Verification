from yacc import ParserPySMT
from pprint import pprint
from pysmt.shortcuts import *

nodes = {
    "init": "x = 5; y = 4; z = 0;",
    "switch" : "",
    "isEven" : "x = 2 * x; y = y / 2;",
    "isOdd" : "y = y - 1; z = z + x;",
    "end" : ""
}

trans = {
    "init" : [("switch", "")],
    "switch" : [("isEven", "y != 0 && (y % 2) == 0 && y == y"), ("isOdd", "y != 0 && (y % 2) != 0"), ("end", "y == 0")],
    "isEven" : [("switch", "")],
    "isOdd" : [("switch", "")],
    "end" : []
}

compiler = ParserPySMT()
prox = {
    "x": Symbol("x", BVType(16)),
    "y": Symbol("y", BVType(16)),
    "z": Symbol("z", BVType(16))
}

curr = {
    "x": Symbol("x", BVType(16)),
    "y": Symbol("y", BVType(16)),
    "z": Symbol("z", BVType(16))
}

for label, cond in trans["switch"]:
    res = compiler.compile(cond)
    print(label, res, eval(res).serialize())

for label, body in nodes.items():
    res = compiler.compile(body)
    print("string", res)
    print("formula", eval(res).serialize())