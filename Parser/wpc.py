from pysmt.shortcuts import *

cfa = {
    "init": (
        "x = 2; y = 4; z = 0;",
        [("switch", "")]
    ),
    "switch": (
        "",
        [("isEven", "y != 0 && (y % 2) == 0"), ("isOdd", "y != 0 && (y % 2) != 0"), ("end", "y == 0")]
    ),
    "isEven": (
        "x = 2 * x; y = y / 2;",
        [("switch", ""), ("overflow", "x*2 < x")]
    ),
    "isOdd": (
        "y = y - 1; z = z + x;",
        "BVSub(y, 1)",
        [("switch", "")]
    ),
    "end": (
        "",
        [("end", "")]
    ),
    "overflow": (
        "",
        [("overflow", "")]
    )
}

state = {
    "variables": ["pc", "x", "y", "z"],
    "size": 8
}




# Variáveis auxiliares à prova
m = Symbol("m", BVType(state["size"]))
n = Symbol("n", BVType(state["size"]))
# Variáveis do programa
x = Symbol("x", BVType(state["size"]))
y = Symbol("y", BVType(state["size"]))
z = Symbol("r", BVType(state["size"]))

# Triple
inv = And(BVUGE(y, BV(0, state["size"])), Equals(BVAdd(BVMul(x, y), z), BVMul(m, n)))
pre = And(BVUGE(m, BV(0, state["size"])), BVUGE(n, BV(0, state["size"])), Equals(z, BV(0, state["size"])), Equals(x, m), Equals(y, n))
pos = Equals(z, BVMul(m, n))

# Assignments
subEven = {
    x: BVMul(x, BV(2, state["size"])),
    y: BVUDiv(y, BV(2, state["size"]))
}
subOdd  = {
    y: BVSub(y, BV(1, state["size"])),
    z: BVAdd(z, x)
}

# Transition conditions
isEven = And(NotEquals(y, BV(0, state["size"])), Equals(BVURem(y, BV(2, state["size"])), BV(0, state["size"])))
isOdd  = And(NotEquals(y, BV(0, state["size"])), NotEquals(BVURem(y, BV(2, state["size"])), BV(0, state["size"])))
isEnd = Equals(y, BV(0, state["size"]))

# Program Flow
fluxoSwitch = And(
    Implies(isEven, substitute(inv, subEven)),
    Implies(isOdd,  substitute(inv, subOdd)),
    Implies(And(isEnd, inv), pos)
)

# Verification condition
vc = Implies(pre, And(inv, ForAll([x, y, z], fluxoSwitch)))