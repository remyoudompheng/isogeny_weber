"""
Iterate over isogenies of degree l out of a given curve.
The base ring must be a finite field.

For 256-bit modulus, this is faster than Sage generic
implementation of isogenies_prime_degree (factors of torsion polynomial).

It it slower for supersingular curves over GF(p^2) (l+1 isogenies)
"""

import argparse
import time

from sage.all import GF, EllipticCurve, next_prime, random_prime, set_verbose
from isogeny_weber import Database, isogenies_prime_degree_weber

if __name__ == "__main__":
    argp = argparse.ArgumentParser()
    argp.add_argument("-v", action="store_true")
    argp.add_argument(
        "--sage", action="store_true", help="Use Sage isogenies_prime_degree"
    )
    argp.add_argument(
        "-j", action="store_true", help="Only benchmark computation of j-invariants"
    )
    argp.add_argument("PBITS", type=int, help="size of modulus")
    argp.add_argument("DATABASE", nargs="?", help="Path to Weber polynomial database")
    args = argp.parse_args()

    set_verbose(1)
    weber_db = Database(args.DATABASE)
    set_verbose(1 if args.v else 0)
    p = random_prime(2**args.PBITS)
    K = GF(p)
    levels = list(weber_db.keys())
    for l in range(min(levels), max(levels), 20):
        l = next_prime(l)
        t0 = time.time()
        print("10 random curves:", end=" ")
        for _ in range(10):
            E = EllipticCurve(K, [K.random_element() for _ in "12"])
            if args.sage:
                print(len(E.isogenies_prime_degree(l)), end=" ")
            else:
                print(
                    len(
                        list(
                            isogenies_prime_degree_weber(E, l, weber_db, only_j=args.j)
                        )
                    ),
                    end=" ",
                )
        print(f"\nTested level {l} in {time.time()-t0:.3f}s")
