"""
Test basic library usage.
"""

from sage.all import GF, EllipticCurve, cputime, proof, set_verbose, next_prime, var
from isogeny_weber import *


def runtest(K, l, A, B, db=None):
    E = EllipticCurve(K, [A, B])
    print(f"degree {l}, {A=} {B=}, {K}")
    t = cputime()
    l = list(isogenies_prime_degree_weber(E, 997, weber_db=db))
    print(f"found {len(l)} isogenies in {cputime(t):.3f}s")
    print(l)


def main():
    import argparse

    argp = argparse.ArgumentParser()
    argp.add_argument("--db", help="optional modular polynomial database file")
    argp.add_argument("-v", action="count")
    args = argp.parse_args()

    set_verbose(args.v)
    db = Database(args.db)
    proof.arithmetic(False)
    runtest(GF(next_prime(2**64)), 127, 12, 34, db=db)
    runtest(GF(next_prime(10**24)), 997, 12, 34, db=db)
    x = var("x")
    K, i = GF((next_prime(10**42), 2), "i", modulus=x**2 + 1).objgen()
    runtest(K, 997, 1 + 2 * i, 3 + 4 * i, db=db)


if __name__ == "__main__":
    main()
