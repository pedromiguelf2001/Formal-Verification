import itertools
from .parser.yacc import ParserPySMT
from pysmt.shortcuts import *
from .plotter import Plotter

DEBUG = False

# PC palavra reservada
class SFOTS(object):
    def __init__(self, cfa, state):
        self.PROGRAM_COUNTER = "pc"
        self.compiler = ParserPySMT()
        self.plotter = Plotter(cfa)
        self.cfa = cfa
        # add pc to variables
        state["variables"] += [self.PROGRAM_COUNTER]
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
        return lambda state : And(userIni(state), Equals(state[self.PROGRAM_COUNTER], BV(0, self.state["size"])))

    def declare(self, i):
        return {name: Symbol(f"{name}_{i}", BVType(self.state["size"])) for name in self.state["variables"]}

    def safety(self, state):
        return And([NotEquals(state[self.PROGRAM_COUNTER], self.indices[key]) for key in self.state["error_states"]])

    def trans(self, curr, prox):
        debug = []
        formulas = []
        for label, (body, trans) in self.cfa.items():
            nodeBody, mutatedState = self.compiler.compile(body) if label not in self.initialNode else ("TRUE()", set())
            preservedVars = [var for var in self.state["variables"] if var not in mutatedState and var != self.PROGRAM_COUNTER]
            preservedFormula = And([Equals(prox[var], curr[var]) for var in preservedVars])
            debug.append(mutatedState)

            for targetNode, cond in trans:
                condFormula, _ = self.compiler.compile(cond)
                formula = And(
                    eval(nodeBody),
                    eval(condFormula),
                    Equals(curr[self.PROGRAM_COUNTER], self.indices[label]),
                    Equals(prox[self.PROGRAM_COUNTER], self.indices[targetNode]),
                    preservedFormula
                )
                debug.append(formula.serialize())
                formulas.append(formula)

        if DEBUG: print("DEBUG", debug, "\n")
        return Or(formulas)

    def declare2(self, i, k):
        return {name: Symbol(f"{name}!{k}_{i}", BVType(self.state["size"])) for name in self.state["variables"]}
    
    def plot(self):
        self.plotter.plot()


# ---------------- Métodos de Prova ----------------
# Bounded model checking
def bmc_always(sfots, k_max):
    for k in range(1, k_max+1):
        trace = [sfots.declare(i) for i in range(k)]

        # adicionar o estado inicial
        initialization = sfots.init(trace[0])
        # adicionar as transições
        transitions = And([sfots.trans(trace[i], trace[i+1]) for i in range(k - 1)])
        # adicionar a negação do invariante
        invariant = Not(And([sfots.safety(trace[i]) for i in range(k-1)]))

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

# k-indução
def kinduction_always(sfots, k):
    trace = [sfots.declare(i) for i in range(k+1)]

    # testar invariante para os estados iniciais (Válidade de P se e só se ~P Unsat)
    initialization = sfots.init(trace[0])
    transitions = And([sfots.trans(trace[i], trace[i+1]) for i in range(k-1)])
    invariant = Or([Not(sfots.safety(trace[i])) for i in range(k)])

    base_case = And(initialization, transitions, invariant)
    model_init = get_model(base_case)

    if model_init:
        print(f"A propiedade falha em pelo menos um dos {k} primeiros estados.")
        for i in trace[0]:
            print(i, "=", model_init[trace[0][i]])
        return False

    # testar invariante para os passos indutivos
    transitions = And([sfots.trans(trace[i], trace[i+1]) for i in range(k)])
    invariant = And([sfots.safety(trace[i]) for i in range(k)])
    inv_final = Not(sfots.safety(trace[k-1]))

    inductive_step = And(transitions, invariant, inv_final)
    model_final = get_model(inductive_step)

    if model_final:
        print("A propiedade falha num dos estados.")
        for i in trace[0]:
            print(i, "=", model_final[trace[0][i]])
        return False

    print("A propriedade é válida!")
    return True

# Interpolantes
def invert(trans):
    return (lambda c, p: trans(p, c))

def baseName(s):
    return ''.join(list(itertools.takewhile(lambda x: x!='!', s)))

def rename(form, state):
    vs = get_free_variables(form)
    pairs = [ (x, state[baseName(x.symbol_name())]) for x in vs ]
    return form.substitute(dict(pairs))

def same(state1, state2):
    return And([Equals(state1[x], state2[x]) for x in state1])

def model_checking_Interpolants(sfots, N, M, k):
        # Criar todos os estados que poderão vir a ser necessários.
        X = [sfots.declare2(i,'X') for i in range(k)]
        Y = [sfots.declare2(i,'Y') for i in range(k)]

        # Estabelecer a ordem pela qual os pares (n,m) vão surgir. Por exemplo:
        order = sorted([(a,b) for a in range(1, N+1) for b in range(1, M+1)], key=lambda tup : tup[0]+tup[1])

        for (n,m) in order:
            Tn = And([sfots.trans(X[i], X[i+1]) for i in range(k - 1)])
            I = sfots.init(X[0])
            Rn = And(I, Tn)

            Bm = And([invert(sfots.trans)(Y[i], Y[i+1]) for i in range(m)])

            E = Not(sfots.safety(Y[0]))
            Um = And(E, Bm)

            Vnm = And(Rn, same(X[n], Y[m]), Um)
            model = get_model(Vnm) 

            if model:
                print("Unsafe")
                return

            # Vnm é instatisfazível
            C = binary_interpolant(And(Rn, same(X[n], Y[m])), Um)

            if C is None:
                print("Interpolant None")
                break

            C0 = rename(C, X[0])
            C1 = rename(C, X[1])
            T = sfots.trans(X[0], X[1])
            #print(And(C0, T, Not(C1)))

            # C é invariante de T
            if not get_model(And(C0, T, Not(C1))):
                print("Safe")
                return

            ### tenta gerar o majorante S
            S = rename(C, X[n])
            while True:
                A = And(S, sfots.trans(X[n], Y[m]))
                if get_model(And(A,Um)):
                    print("Não é possível encontrar um majorante")
                    break

                Cnew = binary_interpolant(A, Um)
                Cn = rename(Cnew, X[n])

                # Se Cn -> S não é tautologia
                if get_model(And(Cn, Not(S))):
                    S = Or(S, Cn)
                else: # S foi encontrado
                    print("fim")
                    print("Safe")
                    return
            print("unknown" )

# Property directed reachability
def at(formula, frame):
    subst = {v: frame["".join(v.symbol_name().split("_")[:-1])] for v in formula.get_free_variables()}
    return formula.substitute(subst)

#lift(sfots, k, Inv, o, s_o)
def craig_interpolation(sfots, k, Inv, Q, s):
    """
    We can implement lift using Craig interpolation between
    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`
    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    frames = [sfots.declare(i) for i in range(k+1)]

    A = at(s, frames[0])
    prec = And(
        at(Inv, frames[0]),
        And([And(at(Q, frames[i]), sfots.trans(frames[i], frames[i+1])) for i in range(k-1)]),
    )
    B = Implies(prec, Not(at(Q, frames[k])))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None

# In this definition Q is a function
def craig_interpolation_f(sfots, k, Inv, Q, s):
    """
    We can implement lift using Craig interpolation between
    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`
    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    frames = [sfots.declare(i) for i in range(k+1)]

    A = at(s, frames[0])
    prec = And(
        at(Inv, frames[0]),
        And([And(Q(frames[i]), sfots.trans(frames[i], frames[i+1])) for i in range(k-1)]),
    )
    B = Implies(prec, Not(Q(frames[k])))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None

def PDR(
    sfots,
    k_init = 1,
    k_max = 15,
    inc = lambda n: n + 1,
    get_currently_known_invariant=lambda: TRUE(),
    pd = True,
    strengthen = lambda k, Inv, o: Inv
):
    """
    Iterative-Deepening k-Induction with Property Direction.
    “Software Verification with PDR: Implementation and Empirical Evaluation of the State of the Art”
    Available at https://arxiv.org/abs/1908.06271.
    """

    # current bound
    k = k_init
    # the invariant computed by this algorithm internally
    InternalInv = TRUE()
    # the set of current proof obligations.
    Obligations = []


    while k <= k_max:
        frames = [sfots.declare(i) for i in range(k+1)]
        transUntil = lambda n : [sfots.trans(frames[i], frames[i+1]) for i in range(n)]
        init = sfots.init(frames[0])

        O_prev = Obligations
        Obligations = []

        # begin: base-case check (BMC)
        # probably have to build something like generate traces
        base_case = And(
            init,
            Or([And(
                And([sfots.trans(frames[i], frames[i+1]) for i in range(n)]),
                Not(sfots.safety(frames[n]))
            ) for n in range(k)])
        )

        if is_sat(base_case):
            # In the future use get_model to provide debugging information
            print("Base case fail", base_case.serialize())
            return False


        # begin: forward-condition check (as described in Sec. 2)
        forward_condition = And(
            init,
            And(transUntil(k))
        )

        if is_unsat(forward_condition):
            print(forward_condition.serialize())
            return True

        # begin: attempt to prove each proof obligation using k-induction
        if pd:
            for o in O_prev:
                # TODO Não sei exatamente como substituir o o[n] por Not(sfots.safety(frames[n]))
                base_case_o = And(
                    init,
                    Or([And(
                        And(transUntil(n)),
                        Not(at(o, frames[n]))
                    ) for n in range(k)])
                )

                if is_sat(base_case_o):
                    print(base_case_o.serialize())
                    return False

                # begin: check the inductive-step case to prove o
                #
                #   sfots.safety(s_n) ⋀_{i=n}^{n+k-1}(P(s_i) ∧ T(s_i,s_{i+1})) ∧ ¬P(s_{n+k})
                #
                step_case_o = And(
                    And([And(at(o, frames[i]), sfots.trans(frames[i], frames[i+1])) for i in range(k)]),
                    Not(at(o, frames[k]))
                )
                ExternalInv = get_currently_known_invariant()
                Inv = And(InternalInv, ExternalInv)
                stepFormula = And(at(Inv, frames[0]), step_case_o)

                if is_sat(stepFormula):
                    # satisfying predecessor state
                    model = get_model(stepFormula)
                    s_o = And([EqualsOrIff(name, val) for name, val in model])
                    cti = craig_interpolation(sfots, k, Inv, o, s_o)
                    if cti:
                        Obligations += [Not(cti)]
                else:
                    InternalInv = And(InternalInv, strengthen(k, Inv, o))


        # begin: check the inductive-step case for the safety property P
        step_case_n = And(
            And([And(sfots.safety(frames[i]), sfots.trans(frames[i], frames[i+1])) for i in range(k)]),
            Not(sfots.safety(frames[k]))
        )
        ExternalInv = get_currently_known_invariant()
        Inv = And(InternalInv, ExternalInv)
        stepFormula = And(at(Inv, frames[0]), step_case_n)

        if is_sat(stepFormula):
            if pd:
                # satisfying predecessor state
                model = get_model(stepFormula)
                s = And([EqualsOrIff(name, val) for name, val in model])
                cti = craig_interpolation_f(sfots, k, Inv, sfots.safety, s)
                if cti:
                    Obligations += [Not(cti)]
        else:
            return True

        k = inc(k)
    print("Property's status is unknown: exceeded maximum number of iterations")
    return None

# ---------------- Main ----------------
if __name__ == "__main__":
    # ---------------- Utilizador ----------------
    bit_vector_multiplication = {
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

    simple_loop = {
        "init": (
            "x = 10;",
            [("loop", "")]
        ),
        "loop": (
            "x = x - 1;",
            [("loop", "x > 1"), ("end", "x == 1"), ("error", "x < 0")]
        ),
        "error": (
            "",
            [("error", "")]
        ),
        "end": (
            "",
            [("end", "")]
        )
    }

    state_loop = {
        "variables": ["pc", "x"],
        "error_states": ["error"],
        "size": 16
    }


    # ---------------- Testes ----------------
    multiplication = SFOTS(bit_vector_multiplication, state)
    loop = SFOTS(simple_loop, state_loop)

    print("\nBMC")
    bmc_always(multiplication, 15)
    print("\nK-Induction")
    kinduction_always(multiplication, 15)
    print("\nInterpolants")
    model_checking_Interpolants(multiplication, 20, 20, 15)