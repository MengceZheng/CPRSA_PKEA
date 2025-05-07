import os
import sys
import time
import logging

from abc import ABCMeta
from abc import abstractmethod

from sage.all import *
from sage.crypto.util import random_blum_prime

import random as rdm

DEBUG_ROOTS = None
BOUND_CHECK = False
USE_FLATTER = False
ACLOG_CLEAR = True

log_file = 'attack.log'  
if ACLOG_CLEAR and os.path.exists(log_file):  
    os.remove(log_file) 
logger = logging.getLogger(__name__)
logging.basicConfig(filename = log_file, level = logging.DEBUG, format = '%(asctime)s - %(levelname)s - %(message)s')


def log_lattice(L):
    """
    Logs a lattice.
    :param L: the lattice
    """
    for row in range(L.nrows()):
        r = ""
        for col in range(L.ncols()):
            if L[row, col] == 0:
                r += "_ "
            else:
                r += "X "
        logging.debug(r)


def create_lattice(pr, shifts, bounds, order="invlex", sort_shifts_reverse=False, sort_monomials_reverse=False):
    """
    Creates a lattice from a list of shift polynomials.
    :param pr: the polynomial ring
    :param shifts: the shifts
    :param bounds: the bounds
    :param order: the order to sort the shifts/monomials by
    :param sort_shifts_reverse: set to true to sort the shifts in reverse order
    :param sort_monomials_reverse: set to true to sort the monomials in reverse order
    :return: a tuple of lattice and list of monomials
    """
    logging.debug(f"Creating a lattice with {len(shifts)} shifts ({order = }, {sort_shifts_reverse = }, {sort_monomials_reverse = })...")
    if pr.ngens() > 1:
        pr_ = pr.change_ring(ZZ, order=order)
        shifts = [pr_(shift) for shift in shifts]

    monomials = set()
    for shift in shifts:
        monomials.update(shift.monomials())

    shifts.sort(reverse=sort_shifts_reverse)
    monomials = sorted(monomials, reverse=sort_monomials_reverse)
    L = matrix(ZZ, len(shifts), len(monomials))
    for row, shift in enumerate(shifts):
        for col, monomial in enumerate(monomials):
            L[row, col] = shift.monomial_coefficient(monomial) * monomial(*bounds)

    monomials = [pr(monomial) for monomial in monomials]
    return L, monomials


def reduce_lattice(L, delta=0.8):
    """
    Reduces a lattice basis using a lattice reduction algorithm (currently LLL).
    :param L: the lattice basis
    :param delta: the delta parameter for LLL (default: 0.8)
    :return: the reduced basis
    """
    # logging.debug(f"Reducing a {L.nrows()} x {L.ncols()} lattice...")
    # return L.LLL(delta)
    start_time = time.perf_counter()
    if USE_FLATTER:
        from subprocess import check_output
        from re import findall
        LL = "[[" + "]\n[".join(" ".join(map(str, row)) for row in L) + "]]"
        ret = check_output(["flatter"], input = LL.encode())
        L_reduced = matrix(L.nrows(), L.ncols(), map(int, findall(rb"-?\d+", ret)))
    else:
        L_reduced = L.LLL(delta)
    end_time = time.perf_counter()
    reduced_time = end_time - start_time
    logging.info(f"Reducing a {L.nrows()} x {L.ncols()} lattice within {reduced_time:.3f} seconds...")
    return L_reduced


def reconstruct_polynomials(B, f, modulus, monomials, bounds, preprocess_polynomial=lambda x: x, divide_gcd=True):
    """
    Reconstructs polynomials from the lattice basis in the monomials.
    :param B: the lattice basis
    :param f: the original polynomial (if set to None, polynomials will not be divided by f if possible)
    :param modulus: the original modulus
    :param monomials: the monomials
    :param bounds: the bounds
    :param preprocess_polynomial: a function which preprocesses a polynomial before it is added to the list (default: identity function)
    :param divide_gcd: if set to True, polynomials will be pairwise divided by their gcd if possible (default: True)
    :return: a list of polynomials
    """
    divide_original = f is not None
    modulus_bound = modulus is not None
    logging.debug(f"Reconstructing polynomials ({divide_original = }, {modulus_bound = }, {divide_gcd = })...")
    polynomials = []
    for row in range(B.nrows()):
        norm_squared = 0
        w = 0
        polynomial = 0
        for col, monomial in enumerate(monomials):
            if B[row, col] == 0:
                continue
            norm_squared += B[row, col] ** 2
            w += 1
            assert B[row, col] % monomial(*bounds) == 0
            polynomial += B[row, col] * monomial // monomial(*bounds)

        # Equivalent to norm >= modulus / sqrt(w)
        # Use BOUND_CHECK = False to achieve a successful attack
        if BOUND_CHECK and modulus_bound and norm_squared * w >= modulus ** 2:
            logging.debug(f"Row {row} is too large, ignoring...")
            continue

        polynomial = preprocess_polynomial(polynomial)

        if divide_original and polynomial % f == 0:
            logging.debug(f"Original polynomial divides reconstructed polynomial at row {row}, dividing...")
            polynomial //= f

        if divide_gcd:
            for i in range(len(polynomials)):
                g = gcd(polynomial, polynomials[i])
                # TODO: why are we only allowed to divide out g if it is constant?
                if g != 1 and g.is_constant():
                    logging.debug(f"Reconstructed polynomial has gcd {g} with polynomial at {i}, dividing...")
                    polynomial //= g
                    polynomials[i] //= g

        if polynomial.is_constant():
            logging.debug(f"Polynomial at row {row} is constant, ignoring...")
            continue

        if DEBUG_ROOTS is not None:
            logging.debug(f"Polynomial at row {row} roots check: {polynomial(*DEBUG_ROOTS)}")

        polynomials.append(polynomial)

    logging.debug(f"Reconstructed {len(polynomials)} polynomials")
    return polynomials


def find_roots_univariate(x, polynomial):
    """
    Returns a generator generating all roots of a univariate polynomial in an unknown.
    :param x: the unknown
    :param polynomial: the polynomial
    :return: a generator generating dicts of (x: root) entries
    """
    if polynomial.is_constant():
        return

    for root in polynomial.roots(multiplicities=False):
        if root != 0:
            yield {x: int(root)}


def find_roots_gcd(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses pairwise gcds to find trivial roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if pr.ngens() != 2:
        return

    logging.debug("Computing pairwise gcds to find trivial roots...")
    x, y = pr.gens()
    for i in range(len(polynomials)):
        for j in range(i):
            g = gcd(polynomials[i], polynomials[j])
            if g.degree() == 1 and g.nvariables() == 2 and g.constant_coefficient() == 0:
                # g = ax + by
                a = int(g.monomial_coefficient(x))
                b = int(g.monomial_coefficient(y))
                yield {x: b, y: a}
                yield {x: -b, y: a}


def find_roots_groebner(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses Groebner bases to find the roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    # We need to change the ring to QQ because groebner_basis is much faster over a field.
    # We also need to change the term order to lexicographic to allow for elimination.
    gens = pr.gens()
    s = Sequence(polynomials, pr.change_ring(QQ, order="lex"))
    while len(s) > 0:
        G = s.groebner_basis()
        logging.debug(f"Sequence length: {len(s)}, Groebner basis length: {len(G)}")
        if len(G) == len(gens):
            logging.debug(f"Found Groebner basis with length {len(gens)}, trying to find roots...")
            roots = {}
            for polynomial in G:
                vars = polynomial.variables()
                if len(vars) == 1:
                    for root in find_roots_univariate(vars[0], polynomial.univariate_polynomial()):
                        roots |= root

            if len(roots) == pr.ngens():
                yield roots
                return

            logging.debug(f"System is underdetermined, trying to find constant root...")
            G = Sequence(s, pr.change_ring(ZZ, order="lex")).groebner_basis()
            vars = tuple(map(lambda x: var(x), gens))
            for solution_dict in solve([polynomial(*vars) for polynomial in G], vars, solution_dict=True):
                logging.debug(solution_dict)
                found = False
                roots = {}
                for i, v in enumerate(vars):
                    s = solution_dict[v]
                    if s.is_constant():
                        if not s.is_zero():
                            found = True
                        roots[gens[i]] = int(s) if s.is_integer() else int(s) + 1
                    else:
                        roots[gens[i]] = 0
                if found:
                    yield roots
                    return

            return
        else:
            # Remove last element (the biggest vector) and try again.
            s.pop()


def find_roots_resultants(gens, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Recursively computes resultants to find the roots.
    :param polynomials: the reconstructed polynomials
    :param gens: the unknowns
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if len(polynomials) == 0:
        return

    if len(gens) == 1:
        if polynomials[0].is_univariate():
            yield from find_roots_univariate(gens[0], polynomials[0].univariate_polynomial())
    else:
        resultants = [polynomials[0].resultant(polynomials[i], gens[0]) for i in range(1, len(gens))]
        for roots in find_roots_resultants(gens[1:], resultants):
            for polynomial in polynomials:
                polynomial = polynomial.subs(roots)
                if polynomial.is_univariate():
                    for root in find_roots_univariate(gens[0], polynomial.univariate_polynomial()):
                        # Show a root 
                        logging.debug(f"Now root is {root}")
                        yield roots | root


def find_roots_variety(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses the Sage variety (triangular decomposition) method to find the roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    # We need to change the ring to QQ because variety requires a field.
    s = Sequence([], pr.change_ring(QQ))
    # We use more polynomials (i.e., poly_number) to find the roots, we can further tweak it
    poly_number = int(len(polynomials) * 0.5)
    for i in range(poly_number):
        s.append(polynomials[i])
    I = s.ideal()
    dim = I.dimension()
    logging.debug(f"Sequence length: {len(s)}, Ideal dimension: {dim}")
    if dim == 0:
        logging.debug("Found ideal with dimension 0, computing variety...")
        logging.debug(f"The variety is {I.variety(ring=ZZ)}")
        for roots in I.variety(ring=ZZ):
            yield {k: int(v) for k, v in roots.items()}

        return
    # for polynomial in polynomials:
    #     s.append(polynomial)
    #     I = s.ideal()
    #     dim = I.dimension()
    #     logging.debug(f"Sequence length: {len(s)}, Ideal dimension: {dim}")
    #     if dim == -1:
    #         s.pop()
    #     elif dim == 0:
    #         logging.debug("Found ideal with dimension 0, computing variety...")
    #         logging.debug(f"The variety is {I.variety(ring=ZZ)}...")
    #         for roots in I.variety(ring=ZZ):
    #             yield {k: int(v) for k, v in roots.items()}

    #         return


def find_roots(pr, polynomials, method="groebner"):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    The method used depends on the method parameter.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :param method: the method to use, can be "groebner", "resultants", or "variety" (default: "groebner")
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if pr.ngens() == 1:
        logging.debug("Using univariate polynomial to find roots...")
        for polynomial in polynomials:
            yield from find_roots_univariate(pr.gen(), polynomial)
    else:
        # Always try this method because it can find roots the others can't.
        yield from find_roots_gcd(pr, polynomials)

        if method == "groebner":
            logging.debug("Using Groebner basis method to find roots...")
            yield from find_roots_groebner(pr, polynomials)
        elif method == "resultants":
            logging.debug("Using resultants method to find roots...")
            yield from find_roots_resultants(pr.gens(), polynomials)
        elif method == "variety":
            logging.debug("Using variety method to find roots...")
            yield from find_roots_variety(pr, polynomials)


class Strategy(metaclass=ABCMeta):
    @abstractmethod
    def generate_S_M(self, f, m):
        """
        Generates the S and M sets.
        :param f: the polynomial
        :param m: the amount of normal shifts to use
        :return: a tuple containing the S and M sets
        """
        pass


class BasicStrategy(Strategy):
    def generate_S_M(self, f, m):
        S = set((f ** (m - 1)).monomials())
        M = set((f ** m).monomials())
        return S, M


class ExtendedStrategy(Strategy):
    def __init__(self, t):
        self.t = t

    def generate_S_M(self, f, m):
        x = f.parent().gens()
        assert len(x) == len(self.t)

        S = set()
        for monomial in (f ** (m - 1)).monomials():
            for xi, ti in zip(x, self.t):
                for j in range(ti + 1):
                    S.add(monomial * xi ** j)

        M = set()
        for monomial in S:
            M.update((monomial * f).monomials())

        return S, M


class Ernst1Strategy(Strategy):
    def __init__(self, t):
        self.t = t

    def generate_S_M(self, f, m):
        x1, x2, x3 = f.parent().gens()

        S = set()
        for i1 in range(m):
            for i2 in range(m - i1):
                for i3 in range(i2 + self.t + 1):
                    S.add(x1 ** i1 * x2 ** i2 * x3 ** i3)

        M = set()
        for i1 in range(m + 1):
            for i2 in range(m - i1 + 1):
                for i3 in range(i2 + self.t + 1):
                    M.add(x1 ** i1 * x2 ** i2 * x3 ** i3)

        return S, M


class Ernst2Strategy(Strategy):
    def __init__(self, t):
        self.t = t

    def generate_S_M(self, f, m):
        x1, x2, x3 = f.parent().gens()

        S = set()
        for i1 in range(m):
            for i2 in range(m - i1 + self.t):
                for i3 in range(m - i1):
                    S.add(x1 ** i1 * x2 ** i2 * x3 ** i3)

        M = set()
        for i1 in range(m + 1):
            for i2 in range(m - i1 + self.t + 1):
                for i3 in range(m - i1 + 1):
                    M.add(x1 ** i1 * x2 ** i2 * x3 ** i3)

        return S, M


def integer_multivariate(f, m, W, X, desired_solution, strategy, roots_method="variety"):
    """
    Computes small integer roots of a multivariate polynomial.
    More information: Jochemsz E., May A., "A Strategy for Finding Roots of Multivariate Polynomials with New Applications in Attacking RSA Variants" (Section 2.2)
    :param f: the polynomial
    :param m: the parameter m
    :param W: the parameter W
    :param X: a list of approximate bounds on the roots for each variable
    :param desired_solution: a list of desired roots for each variable
    :param strategy: the strategy to use (Appendix B)
    :param roots_method: the method to use to find roots (default: "variety") it is more efficient
    :return: a generator generating small roots (tuples) of the polynomial
    """
    pr = f.parent()
    x = pr.gens()
    assert len(x) > 1

    S, M = strategy.generate_S_M(f, m)
    l = [0] * len(x)
    for monomial in S:
        for j, xj in enumerate(x):
            l[j] = max(l[j], monomial.degree(xj))

    a0 = int(f.constant_coefficient())
    assert a0 != 0
    while gcd(a0, W) != 1:
        W += 1

    R = W
    for j, Xj in enumerate(X):
        while gcd(a0, Xj) != 1:
            Xj += 1

        R *= Xj ** l[j]
        X[j] = Xj

    assert gcd(a0, R) == 1
    f_ = (pow(a0, -1, R) * f % R).change_ring(ZZ)

    logging.debug("Generating shifts...")

    shifts = []
    monomials = set()
    for monomial in S:
        g = monomial * f_
        for xj, Xj, lj in zip(x, X, l):
            g *= Xj ** (lj - monomial.degree(xj))

        shifts.append(g)
        monomials.add(monomial)

    for monomial in M:
        if monomial not in S:
            shifts.append(monomial * R)
            monomials.add(monomial)

    logging.info("Generating the lattice...")
    L, monomials = create_lattice(pr, shifts, X)
    logging.info("Reducing the lattice...")
    L = reduce_lattice(L)
    logging.debug(f"Test for original polynomial: f(x0, y0, z0) = {f(desired_solution)}...")
    polynomials = reconstruct_polynomials(L, f, R, monomials, X)
    for poly in polynomials:
        logging.debug(f"The polynomial after reconstructing from lattice vectors: @#$%")
        logging.debug(f"Test for reconstructed g(x0, y0, z0) % R = {poly(desired_solution) % R}")
        logging.debug(f"Test for reconstructed g(x0, y0, z0) = {poly(desired_solution)} over Z")
    start_time = time.perf_counter()
    solution = find_roots(pr, [f] + polynomials, method=roots_method)
    end_time = time.perf_counter()
    solution_time = end_time - start_time
    logging.info(f"Finding roots within {solution_time:.3f} seconds...")
    # for roots in find_roots(pr, [f] + polynomials, method=roots_method):
    for roots in solution:
        yield tuple(roots[xi] for xi in x)


def trivariate_integer_PKEA(N, e, MSB, LSB, delta, delta_MSB, delta_LSB, desired_solution, m=3, t=0):
    """
    Recovers the prime factors of a modulus and the private exponent if some key exposure is given (Common Prime RSA version).
    More information: Zheng M., Nitaj A., "A Novel Partial Key Exposure Attack on Common Prime RSA"
    :param N: the modulus
    :param e: the public exponent
    :param MSB: the most significant bits of the private exponent
    :param LSB: the least significant bits of the private exponent
    :param delta: a predicted bound on the private exponent (d < N^delta)
    :param delta_MSB: the ratio of the bit length of MSB in private key to the modulus bit length
    :param delta_LSB: the ratio of the bit length of LSB in private key to the modulus bit length
    :param desired_solution: a list of desired roots for each variable
    :param m: the m value to use for the small roots method (default: 3)
    :param t: the t value to use for the small roots method (default: automatically computed using m)
    :return: the small solution (tuples) of the trivariate integer polynomial, or None if it was not found
    """
    gamma = 1 - log(e, N)

    modulus_bit_length = int(log(N, 2))
    key_bit_length = int(modulus_bit_length * delta)
    MSB_bit_length = int(modulus_bit_length * delta_MSB)
    LSB_bit_length = int(modulus_bit_length * delta_LSB)

    x, y, z = ZZ["x", "y", "z"].gens()
    dd = MSB * (2 ** (key_bit_length - MSB_bit_length)) + x * (2 ** LSB_bit_length) + LSB
    f = e ** 2 * dd ** 2 + e * dd * (y + z - 2) - (y + z - 1) - (N - 1) * y * z
    logging.debug(f"Generating target polynimial f: {f}")
    X = int(RR(N) ** (delta - delta_MSB - delta_LSB))
    Y = int(RR(N) ** (delta - 1 / 2) * e)  # Equivalent to N^(delta + 1 / 2 - gamma)
    Z = int(RR(N) ** (delta - 1 / 2) * e)  # Equivalent to N^(delta + 1 / 2 - gamma)
    W = int(RR(N) ** (2 * delta) * e ** 2)  # Equivalent to N^(2 * delta + 2 - 2 * gamma)
    # the correct $t$ due to "Revisiting Small Private Key Attacks on Common Prime RSA"
    eta = gamma - delta_MSB - delta_LSB
    t = max(int((sqrt(4 * eta ** 2 + 20 * eta + 13) - 8 * eta - 2) / (3 * (2 * eta + 1)) * m), 0)
    logging.info(f"Trying {m = }, {t = }...")
    strategy = ExtendedStrategy([t, 0, 0])
    solution = integer_multivariate(f, m, W, [X, Y, Z], desired_solution, strategy)
    for x0, y0, z0 in solution:
        dbar, ka, kb = x0, y0, z0
        if dbar != 0 and ka != 0 and kb != 0:
            logging.info(f"Found one possible solution: {dbar = }, {ka = }, {kb = }")
            return dbar, ka, kb

    return None


def generate_common_primes(modulus_bit_length, gamma, lift_ratio=1.2):
    """
    Generate primes for Common Prime RSA with given modulus bit length and gamma. 
    :param modulus_bit_length: The bit length of the modulus.
    :param gamma: The ratio of the bit length of the common prime to the modulus bit length.
    :param lift_ratio: The lift parameter on ensured generation of primes for Common Prime RSA instance. (default: 1.2=6/5)
    :return: A list of p, q, and g for a Common Prime RSA instance, or all zeros if failed.
    """
    N = p = q = a = b = Integer(0)
    common_prime_bit_length = ceil(modulus_bit_length * gamma)
    g = random_blum_prime(2 ** (common_prime_bit_length - 1), 2 ** common_prime_bit_length - 1)
    while True:
        while is_prime(p) or p.nbits() != modulus_bit_length // 2:
            a = rdm.randint(int(2 ** (modulus_bit_length // 2 - 2) * 6 // (g * 5)), 2 ** (modulus_bit_length // 2 - 1) // g)
            p = 2 * g * a + 1
        while is_prime(q) or gcd(a, b) != 1 or q.nbits() != modulus_bit_length // 2:
            b = rdm.randint(int(2 ** (modulus_bit_length // 2 - 2) * 6 // (g * 5)), 2 ** (modulus_bit_length // 2 - 1) // g)
            q = 2 * g * b + 1
        N = p * q
        if N.nbits() == modulus_bit_length:
            return p, q, g
        else:
            return 0, 0, 0


def generate_CPRSA_PKEA_instance(modulus_bit_length, gamma, delta, delta_MSB, delta_LSB, max_attempts=10):
    """
    Generate a Common Prime RSA instance with given modulus bit length, gamma and other parameters. 
    :param modulus_bit_length: The bit length of the modulus.
    :param gamma: The ratio of the bit length of the common prime to the modulus bit length.
    :param delta: The ratio of the bit length of the private key to the modulus bit length.
    :param delta_MSB: The ratio of the bit length of MSB in private key to the modulus bit length.
    :param delta_LSB: The ratio of the bit length of LSB in private key to the modulus bit length.
    :param max_attempts: The maximum number of attempts to generate Common Prime RSA instance. (default: 10)
    :return: A list of the Common Prime RSA instance's parameters and the desired solution, or None if it failed.
    """
    N = p = q = g = a = b = e = d = k = Integer(0)
    attempts = 0
    common_prime_bit_length = ceil(modulus_bit_length * gamma)
    while attempts < max_attempts:
        set_random_seed(int(time.time()))
        while g == 0:
            p, q, g = generate_common_primes(modulus_bit_length, gamma)
        N = p * q
        a = (p - 1) // g // 2
        b = (q - 1) // g // 2
        LCM = 2 * g * a * b
        key_bit_length = int(modulus_bit_length * delta)
        MSB_bit_length = int(modulus_bit_length * delta_MSB)
        LSB_bit_length = int(modulus_bit_length * delta_LSB)
        while gcd(e, N - 1) != 1:
            d = random_blum_prime(2 ** (key_bit_length - 1), 2 ** key_bit_length - 1)
            e = inverse_mod(d, LCM)
        k = (e * d - 1) // 2 // g // a // b
        ak = a * k
        bk = b * k
        MSB = d // (2 ** (key_bit_length - MSB_bit_length))
        LSB = d % (2 ** LSB_bit_length)
        d_bar = (d - MSB * (2 ** (key_bit_length - MSB_bit_length)) - LSB) // (2 ** LSB_bit_length)
        CPRSA_instance = [N, e, p, q, g, d, MSB, LSB]
        desired_solution = [d_bar, ak, bk]
        logging.info(f"Generated a Common Prime RSA instance with {modulus_bit_length}-bit modulus, {common_prime_bit_length}-bit common prime, and {key_bit_length}-bit private key...")
        logging.info(f"Along with {MSB_bit_length}-bit MSB and {LSB_bit_length}-bit LSB...")
        logging.debug(f'p: {p}')
        logging.debug(f'q: {q}')
        logging.debug(f'g: {g}')
        logging.debug(f'a: {a}')
        logging.debug(f'b: {b}')
        logging.debug(f'k: {k}')
        logging.debug(f'N: {N}')
        logging.debug(f'e: {e}')
        logging.debug(f'd: {d}')
        logging.debug(f'MSB: {bin(MSB)[2:]}')
        logging.debug(f'LSB: {bin(LSB)[2:]}')
        logging.debug(f"The desired solution: {d_bar = }, {ak = }, {bk = }")
        return CPRSA_instance, desired_solution
    logging.warning(f"Failed to generate Common Prime RSA instance after {max_attempts} attempts...")
    return None


def attack_CPRSA_PKEA_instance(modulus_bit_length, gamma, delta, delta_MSB, delta_LSB, m=3):
    """
    Partial key exposure attack on Common Prime RSA instance with given parameters
    :param modulus_bit_length: the bit length of the modulus.
    :param gamma: The ratio of the bit length of the common prime to the modulus bit length.
    :param delta: The ratio of the bit length of the private key to the modulus bit length.
    :param delta_MSB: The ratio of the bit length of MSB in private key to the modulus bit length.
    :param delta_LSB: The ratio of the bit length of LSB in private key to the modulus bit length.
    :param m: The given parameter for controlling the lattice dimension. (default: 3)
    :return: 1 if attack succeeds else 0
    """
    result = generate_CPRSA_PKEA_instance(modulus_bit_length, gamma, delta, delta_MSB, delta_LSB)
    if result is not None:
        CPRSA_instance, desired_solution = result
    else:
        print(f"Sorry, cannot generate such a Common Prime RSA instance with given parameters...")
        return 0, 0
    N, e, MSB, LSB = CPRSA_instance[0], CPRSA_instance[1], CPRSA_instance[6], CPRSA_instance[7]
    print(f"The known parameters:\n{N = }\n{e = }\n{MSB = }\n{LSB = }")
    key_bit_length = int(modulus_bit_length * delta)
    MSB_bit_length = int(modulus_bit_length * delta_MSB)
    LSB_bit_length = int(modulus_bit_length * delta_LSB)
    
    start_time = time.perf_counter()
    solution = trivariate_integer_PKEA(N, e, MSB, LSB, delta, delta_MSB, delta_LSB, desired_solution, m)
    end_time = time.perf_counter()
    test_time = end_time - start_time
    if solution is not None:
        dbar, ka, kb = solution
        d = MSB * (2 ** (key_bit_length - MSB_bit_length)) + dbar * (2 ** LSB_bit_length) + LSB
        k = gcd(ka, kb)
        a = ka // k
        b = kb // k
        g = (e * d - 1) // 2 // a // b // k
        p = 2 * g * a + 1
        q = 2 * g * b + 1
        if p * q == N:
            logging.info(f"Succeeded!")
            logging.info(f"Found p = {p}")
            logging.info(f"Found q = {q}")
            print(f"Found primes:\n{p = }\n{q = }")
            return 1, test_time
        else:
            logging.info(f"Failed!")
            return 0, test_time
    else:
        print(f"Sorry, cannot attack this CPRSA instance...")
        return 0, test_time


if __name__ == "__main__":

    if len(sys.argv) == 7: 
        modulus_bit_length, gamma, delta, delta_MSB, delta_LSB, m = int(sys.argv[1]), RR(sys.argv[2]), RR(sys.argv[3]), RR(sys.argv[4]), RR(sys.argv[5]), int(sys.argv[6])
        result, test_time = attack_CPRSA_PKEA_instance(modulus_bit_length, gamma, delta, delta_MSB, delta_LSB, m)
        if result:
            print(f"The attack costs {test_time:.2f} seconds...")

    else:
        print(f"Usage: sage -python attack.py <modulus_bit_length> <gamma> <delta> <delta_MSB> <delta_LSB> <m>")
