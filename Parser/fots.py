import itertools
from yacc import ParserPySMT
from pysmt.shortcuts import *

DEBUG = False

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
        targets = {targetNode for _, transitions in cfa.values() for targetNode, _ in transitions}
        return set(cfa.keys()) - targets

    # Gera função que inicializa o estado na forma (state -> dict)
    def genInit(self):
        ini = list(self.initialNode)[0]
        code, _ = self.compiler.compile(self.cfa[ini][0])
        userIni = eval(f"lambda state: {code.replace('prox', 'state')}")
        return lambda state : And(userIni(state), Equals(state["pc"], BV(0, self.state["size"])))

    def declare(self, i):
        return {name: Symbol(f"{name}_{i}", BVType(self.state["size"])) for name in self.state["variables"]}

    def safety(self, state):
        return And([NotEquals(state["pc"], self.indices[key]) for key in self.state["error_states"]])

    def trans(self, curr, prox):
        debug = []
        formulas = []
        for label, (body, trans) in self.cfa.items():
            nodeBody, mutatedState = self.compiler.compile(body) if label not in self.initialNode else ("TRUE()", set())
            preservedVars = [var for var in self.state["variables"] if var not in mutatedState and var != "pc"]
            preservedFormula = And([Equals(prox[var], curr[var]) for var in preservedVars])
            debug.append(mutatedState)

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

        if DEBUG: print("DEBUG", debug, "\n")
        return Or(formulas)
    
    def error(self, state):
        return Equals(state['pc'], BV(5, 16))

    def declare(self, i):
        return {name: Symbol(f"{name}_{i}", BVType(self.state["size"])) for name in self.state["variables"]}
    
    def declare2(self, i, k):
        return {name: Symbol(f"{name}!{k}_{i}", BVType(self.state["size"])) for name in self.state["variables"]}


# ---------------- Testes ----------------
def bmc_always(fots, k_max):
    for k in range(1, k_max+1):
        trace = [fots.declare(i) for i in range(k)]

        # adicionar o estado inicial
        initialization = fots.init(trace[0])
        # adicionar as transições
        transitions = And([fots.trans(trace[i], trace[i+1]) for i in range(k - 1)])
        # adicionar a negação do invariante
        invariant = Not(And([fots.safety(trace[i]) for i in range(k-1)]))

        formula = And(initialization, transitions, invariant)
        model = get_model(formula)

        if model:
            print(model)
            for i in range(k):
                print("Passo ", i)
                for v in trace[i]:
                    print(v, "=", model[trace[i][v]])
                print("----------------")
            print(f"O invariante não se mantém nos primeiros {k} passos")
        else:
            print(f"O invariante mantém-se nos primeiros {k} passos")


def invert(trans):
    return (lambda c, p: trans(p,c))

def baseName(s):
    return ''.join(list(itertools.takewhile(lambda x: x!='!', s)))

def rename(form,state):
    vs = get_free_variables(form)
    pairs = [ (x,state[baseName(x.symbol_name())]) for x in vs ]
    return form.substitute(dict(pairs))

def same(state1,state2):
    return And([Equals(state1[x],state2[x]) for x in state1])




def model_checking_Interpolants(fots, N, M, k):
        # Criar todos os estados que poderão vir a ser necessários.
        X = [fots.declare2(i,'X') for i in range(k)]
        Y = [fots.declare2(i,'Y') for i in range(k)]
        
        # Estabelecer a ordem pela qual os pares (n,m) vão surgir. Por exemplo:
        order = sorted([(a,b) for a in range(1,N+1) for b in range(1,M+1)],key=lambda tup:tup[0]+tup[1]) 
        
        for (n,m) in order:
            Tn = And([fots.trans(X[i], X[i+1]) for i in range(k - 1)])

            I = fots.init(X[0])
            
            Rn = And(I, Tn)
            
            Bm = And([invert(fots.trans)(Y[i], Y[i+1]) for i in range(m)])
            
            E = fots.error(Y[0])

            Um = And(E, Bm)

            Vnm = And(Rn, same(X[n], Y[m]), Um)
            model = get_model(Vnm) 
             
            if model:
                print("Unsafe")
                return
            else:                        # Vnm é instatisfazível
                C = binary_interpolant(And(Rn, same(X[n], Y[m])), Um)
                
                if C is None:
                    print("Interpolant None")
                    break
                C0 = rename(C, X[0])
                C1 = rename(C, X[1])
                T = fots.trans(X[0], X[1])
                #print(And(C0, T, Not(C1)))
                
                if not get_model(And(C0, T, Not(C1))):   # C é invariante de T
                    print("Safe")
                    return
                else:
                    ### tenta gerar o majorante S
                    S = rename(C, X[n])
                    while True:
                        A = And(S, fots.trans(X[n], Y[m]))
                        if get_model(And(A,Um)):
                            print("Não é possível encontrar um majorante")
                            break
                        else:
                            Cnew = binary_interpolant(A, Um)
                            Cn = rename(Cnew, X[n])
                            if get_model(And(Cn, Not(S))):   # Se Cn -> S não é tautologia
                                S = Or(S, Cn)
                            else:             # S foi encontrado
                                print("fim")
                                print("Safe")
                                return
                            
            print("unknown" )
            
def kinduction_always(fots, inv, k, bits):
    trace = [fots.declare(i) for i in range(k+1)]

    # testar invariante para os estados iniciais (Válidade de P se e só se ~P Unsat)
    initialization = fots.init(trace[0]) 
   
    transitions = And([fots.trans(trace[i], trace[i+1]) for i in range(k-1)])   

    invariant = Or([Not(inv(trace[i], bits)) for i in range(k)])

    sat = And(initialization, transitions, invariant)
    model_init = get_model(sat)

    if model_init:
        print('A propiedade falha em pelo menos um dos', k, ' primeiros estados.')
        for i in trace[0]:
            print(i,' = ', model_init[trace[0][i]])
        return
        
    transitions2 = And([fots.trans(trace[i], trace[i+1]) for i in range(k)])

    invariant2 = And([inv(trace[i], bits) for i in range(k)])

    inv_final = (Not(inv(trace[k-1], bits)))

    pass_indutivo = And(transitions2, invariant2, inv_final)
    model_final = get_model(pass_indutivo)

    if model_final:
        print('A propiedade falha num dos estados.')
        for i in trace[0]:
            print(i,' = ', model_final[trace[0][i]])
        return
    
    #if s.check() == unknown:
    #    print('Inconclusivo...')
    #    return

    print('A propriedade é válida!')
   






# propriedade de segurança
def check_inv(state, n):
    # pc não atingir estado de erro
    return NotEquals(state["pc"], BV(5, n))

# ---------------- Main ----------------
fots = FOTS(cfa, state)

form = BVUGT(BVMul(BV(65534, 16), BV(2, 16)), BV(65534, 16))
model = get_model(form)

#bmc_always(fots, check_inv, 15)
#model_checking_Interpolants(fots, 20, 20, 15)
#kinduction_always(fots, check_inv, 20, 16)


# ---------------- Main ----------------
if __name__ == "__main__":
    # ---------------- Utilizador ----------------
    cfa = {
        "init": (
            "x = 3; y = 4; z = 0;",
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
        "error_states": ["overflow"],
        "size": 16
    }

    fots = FOTS(cfa, state)

    bmc_always(fots, 15)

