"""
Test database by checking the existence of isogenies for j-invariants
linked by the modular polynomials.
"""

import argparse
import time

from sage.all import GF, EllipticCurve_from_j, random_prime, set_verbose
from isogeny_weber import Database, isogenies_prime_degree_weber

if __name__ == "__main__":
    argp = argparse.ArgumentParser()
    argp.add_argument("-v", action="store_true")
    argp.add_argument("DATABASE", nargs="?", help="Path to Weber polynomial database")
    args = argp.parse_args()

    if args.v:
        set_verbose(1)
    weber_db = Database(args.DATABASE)

    for l in weber_db.keys():
        t0 = time.time()
        print("Random moduli:", end=" ")
        points = 0
        for _ in range(3):
            # Test 3 primes and 10 values per prime
            p = random_prime(2**30)
            K = GF(p)
            print(p, end=" ")
            count = 0
            while count < 10:
                f = K.random_element()
                j = (f**24 - 16) ** 3 / f**24
                E = EllipticCurve_from_j(j)
                wp = weber_db.modular_polynomial(l, base_ring=K, y=f)
                phis = list(isogenies_prime_degree_weber(E, l, weber_db))
                j2s = [(_f**24 - 16) ** 3 / _f**24 for _f, _ in wp.roots()]
                if j2s:
                    count += 1
                    points += len(wp.roots())
                assert set(phi.codomain().j_invariant() for phi in phis) == set(j2s)
        print(f"\nTested level {l} in {time.time()-t0:.3f}s ({points} modular points)")
