from pysmt.shortcuts import *

def _lift(k, Inv, Q, s, T):
    """
    We can implement lift using Craig interpolation between
    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`
    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    A = s[0]
    B = (Inv[0] &
         Q[:k - 1] &
         T[:k - 1]
         ).Implies(Not(Q @ k))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None

def PDR(
    I,
    T,
    P,
    k_init = 1,
    k_max = int(float('inf')),
    inc = lambda n: n + 1,
    get_currently_known_invariant=lambda: TRUE(),
    pd = True,
    lift = _lift,
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
    Obligations = set()


    while k <= k_max:
        O_prev = Obligations
        Obligations = set()

        # begin: base-case check (BMC)
        # probably have to build something like generate traces
        base_case = And(I[0], Or([And(T[:n - 1], Not(P[n])) for n in range(k)]))

        if is_sat(base_case):
            # In the future use get_model to provide debugging information
            return False


        # begin: forward-condition check (as described in Sec. 2)
        forward_condition = And(I[0], T[:k - 1])

        if is_unsat(forward_condition):
            print(forward_condition.serialize())
            return True


        # begin: attempt to prove each proof obligation using k-induction
        if pd:
            for o in O_prev:
                # begin: check the base case for a proof obligation o
                base_case_o = And(I[0], Or([And(T[:n - 1], Not(o[n])) for n in range(k)]))

                if is_sat(base_case_o):
                    return False

                # begin: check the inductive-step case to prove o
                #
                #   Inv(s_n) ⋀_{i=n}^{n+k-1}(P(s_i) ∧ T(s_i,s_{i+1})) ∧ ¬P(s_{n+k})
                #
                step_case_o = And(
                    And(o[:k - 1], T[:k - 1]),
                    Not(o[k])
                )
                ExternalInv = get_currently_known_invariant()
                Inv = And(InternalInv, ExternalInv)

                if is_sat(And(Inv[0], step_case_o)):
                    s_o = None#satifying predecessor state
                    Obligations |= (Obligations, Not(lift(k, Inv, o, s_o)))
                else:
                    InternalInv = And(InternalInv, strengthen(k, Inv, o))


        # begin: check the inductive-step case for the safety property P
        step_case_n = And(
            And(P[:k - 1], T[:k - 1]),
            Not(P[k])
        )
        ExternalInv = get_currently_known_invariant()
        Inv = And(InternalInv, ExternalInv)

        if is_sat(And(Inv[0], step_case_n)):
            if pd:
                s = None#satifying predecessor state
                Obligations |= (Obligations, Not(lift(k, Inv, P, s)))
        else:
            return True

        k = inc(k)
    print("Property's status is unknown: exceeded maximum number of iterations")
    return None