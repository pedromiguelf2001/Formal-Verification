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

def proveSMT(formula):
    print("Serialization of the formula:")
    formula = Not(formula)
    print(formula.serialize())
    print("Simplification of the formula:")
    print(formula.simplify().serialize())

    with Solver(name="z3") as solver:
        solver.add_assertion(formula)
        if not solver.solve():
            print("Proved")
        else:
            print("Failed to prove")
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

safety = BVUGE(BVAdd(x, x), x)
pre = And(Equals(x, BV(70, 8)), Equals(y, BV(4, 8)), Equals(z, zero), Equals(pc, one))
pos = TRUE()

# Attribuições
# s1
subSwitch = dict()
# s2
subEven = {
    y: BVUDiv(y, BV(2, 8)),
    x: BVMul(x, BV(2, 8)),
}
# s3
subOdd = {
    y: BVSub(y, BV(1, 8)),
    z: BVAdd(z, x)
}
# s4
subEnd = dict()
# s5
subOverflow = dict()

# Escolha não-determinística
# Condições
isEven = And(Equals(pc, one), NotEquals(y, zero), Equals(BVURem(y, BV(2, 8)), zero))
isOdd  = And(Equals(pc, one), NotEquals(y, zero), NotEquals(BVURem(y, BV(2, 8)), zero))
isEnd  = And(Equals(pc, one), Equals(y, zero))
# back to switch
isOverflow = And(Equals(pc, BV(2, 8)), BVULT(BVMul(x, BV(2, 8)), x))
isSwitch   = And(Equals(pc, BV(2, 8)), BVUGE(BVMul(x, BV(2, 8)), x))
fluxoOdd = And(Equals(pc, BV(3, 8)), TRUE())
# remain in terminal states
# vc = generator(safety, substitutions)
# fs = generator(safety, substitutions)

# for f in fs:
#     vc = Implies(pre, And(safety, f))
#     proveSMT(vc)
fluxoEnd = And(Equals(pc, BV(4, 8)), TRUE())
fluxoOverflow = And(Equals(pc, BV(5, 8)), TRUE())

def transition(formula):
    return Or(
        Implies(And(isEven, formula), substitute(formula, subEven)),
        Implies(And(isOdd, formula), substitute(formula, subOdd)),
        Implies(And(isEnd, formula), substitute(formula, subEnd)),
        Implies(And(isOverflow, formula), substitute(formula, subOverflow)),
        Implies(And(isSwitch, formula), substitute(formula, subSwitch)),
        Implies(And(fluxoOdd, formula), substitute(formula, subSwitch)),
        Implies(And(fluxoEnd, formula), substitute(formula, subEnd)),
        Implies(And(fluxoOverflow, formula), substitute(formula, subOverflow)),
    )

substitutions = [
    (subSwitch, BV(1, 8)),
    (subEven, BV(2, 8)),
    (subOdd, BV(3, 8)),
    (subEnd, BV(4, 8)),
    (subOverflow, BV(5, 8)),
]

def newWay(formulas, substitutions):
    return [
        (substitute(formula, sub), state)
        for formula in formulas
        for sub, state in substitutions
    ]

def generator(start, substitutions, iterations=3):
    form = [start]
    for _ in range(iterations):
        form = newWay(form, substitutions)
    return form

f = safety
for i in range(3):
    f = transition(f)
vc = Implies(pre, And(safety, f))
proveSMT(vc)

#vc = Implies(pre, And(safety, ForAll([x, y, z], fluxoSwitch)))


# vc = generator(safety, substitutions)
# fs = generator(safety, substitutions)

# for f in fs:
#     vc = Implies(pre, And(safety, f))
#     proveSMT(vc)