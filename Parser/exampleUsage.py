from yacc import ParserPySMT
from pprint import pprint
from pysmt.shortcuts import *

# ---------------- Utilizador ----------------
cfa = {
    "init": (
        "x = 5; y = 4; z = 0;",
        [("switch", "")]
    ),
    "switch": (
        "",
        [("isEven", "y != 0 && (y % 2) == 0"), ("isOdd", "y != 0 && (y % 2) != 0"), ("end", "y == 0")]
    ),
    "isEven": (
        "x = 2 * x; y = y / 2;",
        [("switch", "")]
    ),
    "isOdd": (
        "y = y - 1; z = z + x;",
        [("switch", "")]
    ),
    "end": (
        "",
        [("end", "")]
    )
}

state = {
    "variables": ["pc", "x", "y", "z"],
    "size": 16
}

# ---------------- Nossas funções ----------------
def genState(vars, i, n):
    return {name: Symbol(f"{name}_{i}", BVType(n)) for name in vars}

def init(state):
    return And(
        Equals(state["pc"], BV(0, 16)),
        Equals(state["x"], BV(5, 16)),
        Equals(state["y"], BV(4, 16)),
        Equals(state["z"], BV(0, 16))
    )

compiler = ParserPySMT()

indices = {key: BV(i, 16) for i, key in enumerate(cfa.keys())}

# find start node
targets = set()
for _, transitions in cfa.values():
    for targetNode, _ in transitions:
        targets.add(targetNode)

initialNode = set(cfa.keys()) - targets

print(initialNode)
# end find start node

def trans(curr, prox):
    formulas = []
    for label, (body, trans) in cfa.items():
        nodeBody = compiler.compile(body)
        if label in initialNode:
            nodeBody = nodeBody.replace("prox", "curr")

        for targetNode, cond in trans:
            formula = And(
                eval(nodeBody),
                eval(compiler.compile(cond)),
                Equals(curr["pc"], indices[label]),
                Equals(prox["pc"], indices[targetNode])
            )
            print(formula.serialize())
            formulas.append(formula)

    return Or(formulas)

# TODO: preservar variáveis

# ---------------- Aplicação ----------------
curr = genState(state["variables"], 0, state["size"])
prox = genState(state["variables"], 1, state["size"])
formula = trans(curr, prox)

print()
print(formula.serialize())