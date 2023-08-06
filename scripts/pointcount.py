"""
Simple test script for point counting function.
"""

import argparse
from sage.all import *
from isogeny_weber import *


def main():
    argp = argparse.ArgumentParser()
    argp.add_argument("-v", action="count", default=0)
    argp.add_argument("--db", help="Path to Weber polynomial database")
    argp.add_argument(
        "--repeat", type=int, default=1, help="Number of tests to perform"
    )
    argp.add_argument("PBITS", type=int, help="size of modulus or modulus itself")
    args = argp.parse_args()

    # FIXME: spurious is_prime in Polynomial.factor
    proof.arithmetic(False)
    pari.allocatemem(4 << 30)

    set_verbose(1)
    weber_db = Database(args.db)
    set_verbose(args.v)

    if is_prime(args.PBITS) and args.PBITS > 2 * max(weber_db.keys()):
        p = args.PBITS  # prime number provided
    else:
        p = random_prime(2**args.PBITS)

    A, B = 123, 456
    for _ in range(args.repeat):
        K = GF(p)
        if K(4 * A**3 + 27 * B**2) == 0:
            print(f"Invalid parameters {p=} {A=} {B=}")
            break
        E = EllipticCurve(K, [A, B])
        print(E)
        tr = trace_of_frobenius(E, weber_db=weber_db)
        print("Trace of Frobenius:", tr)
        print("Order:", E.order())
        if p != args.PBITS:
            p = random_prime(2**args.PBITS)
        else:
            A, B = K.random_element(), K.random_element()


if __name__ == "__main__":
    main()
