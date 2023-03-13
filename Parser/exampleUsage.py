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
# end find start node

def genInit():
    ini = list(initialNode)[0]
    code, vars = compiler.compile(cfa[ini][0])
    func = f"lambda state: {code.replace('prox', 'state')}"
    #print(code,func)
    return eval(func)

def trans(curr, prox):
    debug = []
    formulas = []
    for label, (body, trans) in cfa.items():
        nodeBody, mutatedState = compiler.compile(body)
        if label in initialNode:
            nodeBody = "TRUE()"#nodeBody.replace("prox", "curr")
            mutatedState = set()
        
        debug.append(mutatedState)
        preservedVars = [var for var in state["variables"] if var not in mutatedState and var != "pc"]
        preservedFormula = And([Equals(prox[var], curr[var]) for var in preservedVars])

        for targetNode, cond in trans:
            condFormula, _ = compiler.compile(cond)
            formula = And(
                eval(nodeBody),
                eval(condFormula),
                Equals(curr["pc"], indices[label]),
                Equals(prox["pc"], indices[targetNode]),
                preservedFormula
            )
            debug.append(formula.serialize())
            formulas.append(formula)

    return Or(formulas)

# ---------------- Aplicação ----------------
# curr = genState(state["variables"], 0, state["size"])
# prox = genState(state["variables"], 1, state["size"])
# formula = trans(curr, prox)

print()
# print(formula.serialize())

# ---------------- Testes ----------------
def bmc_always(declare, init, trans, inv, K, n):
    for k in range(1,K+1):
        formula = TRUE()

        trace = [declare(state["variables"], i, state["size"]) for i in range(k)]
        initializer = genInit()
        inited = And(
            initializer(trace[0]),
            Equals(trace[0]["pc"], BV(0, 16))
        )
        print(inited)
        # adicionar o estado inicial
        formula = And(formula, inited)
        # formula = And(formula, And(
        #     Equals(trace[0]["pc"], BV(0, 16)),
        #     Equals(trace[0]["x"], BV(5, 16)),
        #     Equals(trace[0]["y"], BV(4, 16)),
        #     Equals(trace[0]["z"], BV(0, 16))
        # ))
        
        for i in range(k - 1):
            formula = And(formula, And(trans(trace[i], trace[i+1])))
            
        # adicionar a negação do invariante
        formula = And(formula, (And([inv(trace[i], 5, 4, n) for i in range(k-1)])))

        model = get_model(formula)

        if model:
            print(model)
            for i in range(k):
                print("Passo ", i)
                for v in trace[i]:
                    print(v, "=", model[trace[i][v]])
                print("----------------")
            print("O invariante não se mantém nos primeiros", k, "passos")
            #return None
        else:
            print(formula)
        
    print(f"O invariante mantém-se nos primeiros {K} passos")

# invariante -> x*y+z = a*b
def check_inv(state, a, b, n):
    return Equals(BVAdd(BVMul(state['x'], state['y']), state['z']), BVMul(BV(a, 16), BV(b, 16)))

bmc_always(genState, init, trans, check_inv, 15, 16)



