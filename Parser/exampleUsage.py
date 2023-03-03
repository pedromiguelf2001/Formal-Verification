from yacc import ParserPySMT
from pprint import pprint

nodes = {
    "init": "x = 5; y = 4; z = 0;",
    "switch" : "",
    "isEven" : "x = 2 * x; y = y / 2;",
    "isOdd" : "y = y - 1; z = z + x;",
    "end" : ""
}

trans = {
    "init" : [("switch", "")],
    "switch" : [("isEven", "y != 0 && (y % 2) == 0"), ("isOdd", "y != 0 && (y % 2) != 0"), ("end", "y == 0")],
    "isEven" : [("switch", "")],
    "isOdd" : [("switch", "")],
    "end" : []
}

compiler = ParserPySMT()

for label, body in nodes.items():
    print(compiler.compile(body))