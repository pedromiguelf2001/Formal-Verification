from yacc import ParserPySMT
from pprint import pprint
from pysmt.shortcuts import *


# ---------------- Utilizador ----------------
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
    "size": 16
}

# PC palavra reservada
class FOTS(object):
    def __init__(self, cfa, state):
        self.compiler = ParserPySMT()
        self.cfa = cfa
        self.state = state
        self.initialNode = self.findStartNode(self.cfa)
        self.indices = {key: BV(i, 16) for i, key in enumerate(self.cfa.keys())}
        self.init = self.genInit()

    def findStartNode(self, cfa):
        targets = set()
        for _, transitions in cfa.values():
            for targetNode, _ in transitions:
                targets.add(targetNode)

        return set(cfa.keys()) - targets

    # gera função que inicializa o estado na forma (state -> dict)
    def genInit(self):
        ini = list(self.initialNode)[0]
        code, _ = self.compiler.compile(cfa[ini][0])
        userIni = eval(f"lambda state: {code.replace('prox', 'state')}")
        func =  lambda state : And(userIni(state), Equals(state["pc"], BV(0, self.state["size"])))
        return func

    def trans(self, curr, prox):
        debug = []
        formulas = []
        for label, (body, trans) in cfa.items():
            nodeBody, mutatedState = self.compiler.compile(body) if label not in self.initialNode else ("TRUE()", set())

            debug.append(mutatedState)
            preservedVars = [var for var in self.state["variables"] if var not in mutatedState and var != "pc"]
            preservedFormula = And([Equals(prox[var], curr[var]) for var in preservedVars])

            for targetNode, cond in trans:
                condFormula, _ = self.compiler.compile(cond)
                formula = And(
                    eval(nodeBody),
                    eval(condFormula),
                    Equals(curr["pc"], self.indices[label]),
                    Equals(prox["pc"], self.indices[targetNode]),
                    preservedFormula
                )
                debug.append(formula.serialize())
                formulas.append(formula)

        return Or(formulas)
    
    def declare(self, i):
        return {name: Symbol(f"{name}_{i}", BVType(self.state["size"])) for name in self.state["variables"]}



# ---------------- Testes ----------------
def bmc_always(fots, inv, K):
    for k in range(1,K+1):
        trace = [fots.declare(i) for i in range(k)]

        # adicionar o estado inicial
        initialization = fots.init(trace[0])
        # adicionar as transições
        transitions = And([fots.trans(trace[i], trace[i+1]) for i in range(k - 1)])
        # adicionar a negação do invariante
        invariant = Not(And([inv(trace[i], 16) for i in range(k-1)]))

        formula = And(initialization, transitions, invariant)
        model = get_model(formula)

        if model:
            print(model)
            for i in range(k):
                print("Passo ", i)
                for v in trace[i]:
                    print(v, "=", model[trace[i][v]])
                print("----------------")
            print("O invariante não se mantém nos primeiros", k, "passos")
        else:
            print(formula)
            print(f"O invariante mantém-se nos primeiros {K} passos")

# propriedade de segurança
def check_inv(state, n):
    # pc não atingir estado de erro
    return NotEquals(state["pc"], BV(5, n))

# ---------------- Main ----------------
fots = FOTS(cfa, state)

bmc_always(fots, check_inv, 15)
