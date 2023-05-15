from fots import FOTS
from pysmt.shortcuts import *

def at(formula, frame):
    subst = {v: frame["".join(v.symbol_name().split("_")[:-1])] for v in formula.get_free_variables()}
    return formula.substitute(subst)

#lift(fots, k, Inv, o, s_o)
def craig_interpolation(fots, k, Inv, Q, s):
    """
    We can implement lift using Craig interpolation between
    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`
    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    frames = [fots.declare(i) for i in range(k+1)]

    A = at(s, frames[0])
    prec = And(
        at(Inv, frames[0]),
        And([And(at(Q, frames[i]), fots.trans(frames[i], frames[i+1])) for i in range(k-1)]),
    )
    B = Implies(prec, Not(at(Q, frames[k])))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None

def craig_interpolation_func(fots, k, Inv, Q, s):
    """
    We can implement lift using Craig interpolation between
    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`
    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    frames = [fots.declare(i) for i in range(k+1)]

    A = at(s, frames[0])
    prec = And(
        at(Inv, frames[0]),
        And([And(Q(frames[i]), fots.trans(frames[i], frames[i+1])) for i in range(k-1)]),
    )
    B = Implies(prec, Not(Q(frames[k])))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None

def PDR(
    fots,
    k_init = 1,
    k_max = 15,#int(float('inf')),
    inc = lambda n: n + 1,
    get_currently_known_invariant=lambda: TRUE(),
    pd = True,
    lift = craig_interpolation,
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

    # safety property
    sp = lambda state : NotEquals(state["pc"], BV(5, 16))
    #sp = lambda state : BVUGE(state["x"], BV(0, 16))


    while k <= k_max:
        print("k = ", k)
        frames = [fots.declare(i) for i in range(k+1)]
        transUntil = lambda n : [fots.trans(frames[i], frames[i+1]) for i in range(n)]
        init = fots.init(frames[0])

        O_prev = Obligations
        Obligations = []

        # begin: base-case check (BMC)
        # probably have to build something like generate traces
        base_case = And(
            init,
            Or([And(
                And([fots.trans(frames[i], frames[i+1]) for i in range(n)]),
                Not(sp(frames[n]))
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
                # TODO Não sei exatamente como substituir o o[n] por Not(sp(frames[n]))
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
                #   Inv(s_n) ⋀_{i=n}^{n+k-1}(P(s_i) ∧ T(s_i,s_{i+1})) ∧ ¬P(s_{n+k})
                #
                step_case_o = And(
                    And([And(at(o, frames[i]), fots.trans(frames[i], frames[i+1])) for i in range(k)]),
                    Not(at(o, frames[k]))
                )
                ExternalInv = get_currently_known_invariant()
                Inv = And(InternalInv, ExternalInv)
                stepFormula = And(at(Inv, frames[0]), step_case_o)

                if is_sat(stepFormula):
                    # satisfying predecessor state
                    model = get_model(stepFormula)
                    s_o = And([EqualsOrIff(name, val) for name, val in model])
                    cti = craig_interpolation(fots, k, Inv, o, s_o)
                    if cti:
                        Obligations += [Not(cti)]
                else:
                    InternalInv = And(InternalInv, strengthen(k, Inv, o))


        # begin: check the inductive-step case for the safety property P
        step_case_n = And(
            And([And(sp(frames[i]), fots.trans(frames[i], frames[i+1])) for i in range(k)]),
            Not(sp(frames[k]))
        )
        ExternalInv = get_currently_known_invariant()
        Inv = And(InternalInv, ExternalInv)
        stepFormula = And(at(Inv, frames[0]), step_case_n)

        if is_sat(stepFormula):
            if pd:
                # satisfying predecessor state
                model = get_model(stepFormula)
                s = And([EqualsOrIff(name, val) for name, val in model])
                cti = craig_interpolation_func(fots, k, Inv, sp, s)
                if cti:
                    Obligations += [Not(cti)]
        else:
            return True

        k = inc(k)
    print("Property's status is unknown: exceeded maximum number of iterations")
    return None

cfa = {
    "init": (
        "x = 65000; y = 2; z = 0;",
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
    "size": 16
}
fots = FOTS(cfa, state)

cfas = {
    "init": (
        "x = 10;",
        [("loop", "")]
    ),
    "loop": (
        "x = x - 1;",
        [("loop", "x > 1"), ("end", "x <= 1")]
    ),
    "end": (
        "",
        [("end", "")]
    )
}

states = {
    "variables": ["pc", "x"],
    "size": 16
}


simple = FOTS(cfas, states)
res = PDR(fots, 1, 15)

print("result:", res)