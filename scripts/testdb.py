"""
Test database by checking the existence of isogenies for j-invariants
linked by the modular polynomials.

This is equivalent to finding coordinates of points
of modular curves modulo random primes.

If a numerical argument MAXL is supplied, polynomials will be computed
on-the-fly.
"""

import argparse
import os
import time

from sage.all import (
    GF,
    EllipticCurve_from_j,
    random_prime,
    legendre_symbol,
    set_verbose,
    primes
)
from isogeny_weber import Database, isogenies_prime_degree_weber

if __name__ == "__main__":
    argp = argparse.ArgumentParser()
    argp.add_argument("-v", action="store_true")
    argp.add_argument("--fast", action="store_true")
    argp.add_argument("PBITS", type=int, help="modulus size")
    argp.add_argument(metavar="MAXL|DATABASE", dest="database", nargs="?", help="Path to Weber polynomial database")
    args = argp.parse_args()

    if args.v:
        set_verbose(1)
    if args.database.isdigit():
        weber_db = Database()
        ls = primes(5, int(args.database) + 1)
    else:
        weber_db = Database(args.database)
        ls = list(weber_db.keys())

    for l in ls:
        t0 = time.time()
        print("Random moduli:", end=" ")
        points = 0
        for _ in range(3):
            # Test 3 primes and 10 values per prime
            p = random_prime(2**args.PBITS, lbound=2 ** (args.PBITS - 1))
            if p <= 4 * l:
                continue
            K = GF(p)
            print(p, end=" ")
            count = 0
            while count < (1 if args.fast else 10):
                j = 0
                while j == 0 or j == 1728:
                    j = K.random_element()
                E = EllipticCurve_from_j(j)
                D = E.trace_of_frobenius() ** 2 - 4 * p
                phis = list(isogenies_prime_degree_weber(E, l, weber_db))
                if len(phis) == l + 1:
                    # May happen sometimes
                    assert E.is_supersingular() or legendre_symbol(D, l) == 0
                    # assert l + 1 == len(E.isogenies_prime_degree(l))
                else:
                    # Is l an Atkin/Elkies prime?
                    assert len(phis) == legendre_symbol(D, l) + 1, (D, l, phis)
                if phis:
                    count += 1
                    points += len(phis)
        print(f"\nTested level {l} in {time.time()-t0:.3f}s ({points} modular points)")
