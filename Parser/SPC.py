from pysmt.shortcuts import *
import pysmt.typing as pt

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
        [("switch", "x*2 >= x"), ("overflow", "x*2 < x")]
    ),
    "isOdd": (
        "y = y - 1; z = z + x;",
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

def getCore(formula):
    from pysmt.rewritings import conjunctive_partition
    conj = conjunctive_partition(formula)
    ucore = get_unsat_core(conj)
    print(f"UNSAT-Core size {len(ucore)}")
    for f in ucore:
        print(f.serialize())

def getVars(formula, solver):
    model = get_model(formula)
    for l in [x for x in formula.get_free_variables()]:
        print(f"{l} = {model.get_value(l)}")
    print(model)


bits = 8
zero = BV(0, 8)
one  = BV(1, 8)

# O ciclo
x = Symbol("x", pt.BV8)
y = Symbol("y", pt.BV8)
z = Symbol("z", pt.BV8)
pc = Symbol("pc", pt.BV8)

variables = [x, y, z, pc]

safety = Not(Equals(pc, BV(5, 8)))
init = And(Equals(x, BV(2, 8)), Equals(y, BV(4, 8)), Equals(z, zero), Equals(pc, zero))

# Attribuições
subSwitch = {
    pc: one,
}
subEven = {
    pc: BV(2, 8),
    y: BVUDiv(y, BV(2, 8)),
    x: BVMul(x, BV(2, 8)),
}
subOdd = {
    pc: BV(3, 8),
    y: BVSub(y, BV(1, 8)),
    z: BVAdd(z, x)
}
subEnd = {
    pc: BV(4, 8),
}
subOverflow = {
    pc: BV(5, 8),
}

# Escolha não-determinística
# Condições
isEven = And(NotEquals(y, zero), Equals(BVURem(y, BV(2, 8)), zero))
isOdd  = And(NotEquals(y, zero), NotEquals(BVURem(y, BV(2, 8)), zero))
isEnd = Equals(y, zero)
isOverflow = BVULT(BVMul(x, BV(2, 8)), x)
isSwitch = BVUGE(BVMul(x, BV(2, 8)), x)
# Fluxos

a = Symbol("a", pt.BV8)

t01 = And(Equals(pc, zero), TRUE())
t12 = And(Equals(pc, one), isEven)
t13 = And(Equals(pc, one), isOdd)
t14 = And(Equals(pc, one), isEnd)
t21 = And(Equals(pc, BV(2, 8)), isSwitch)
t25 = And(Equals(pc, BV(2, 8)), isOverflow)
t31 = And(Equals(pc, BV(3, 8)), TRUE())
t44 = And(Equals(pc, BV(4, 8)), TRUE())
t55 = And(Equals(pc, BV(5, 8)), TRUE())

def trans(formula):
    return Or(
        Implies(t01, substitute(formula, )),
        Implies(t12, ),
        Implies(t13, ),
        Implies(t14, ),
        Implies(t21, ),
        Implies(t25, ),
        Implies(t31, ),
        Implies(t44, ),
        Implies(t55, )
    )

f = safety

k = 10
vc = init
for i in k:
    vc = Implies(vc, And(trans(vc), safety))



def proveSMT(formula):
    print("Serialization of the formula:")
    formula = Not(formula)
    print(formula.serialize())

    with Solver(name="z3") as solver:
        solver.add_assertion(formula)
        if not solver.solve():
            print("Proved")
        else:
            print("Failed to prove")
            getVars(formula, solver)


proveSMT(vc)