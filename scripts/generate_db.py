"""
Generation utility for the Weber modular polynomial database.

This utility does not read input files and computes
all polynomials as needed.

A few minutes are enough to generate all polynomials for prime l < 1000.
About one hour is needed to generate all polynomials for prime l < 2000.
"""

import argparse
import sys

from sage.all import primes
from isogeny_weber import poldb_encode
from isogeny_weber.poldb_compute import compute_weber_modular_poly

if __name__ == "__main__":
    argp = argparse.ArgumentParser()
    argp.add_argument("--min", default=5, type=int)
    argp.add_argument("OUTPUT")
    argp.add_argument("MAXPRIME")
    args = argp.parse_args()

    with open(args.OUTPUT, "wb") as w:
        for l in primes(args.min, args.MAXPRIME):
            poly = compute_weber_modular_poly(l)
            coeffs = [(a, b, c) for (a, b), c in poly.items()]
            if l == 29:
                print(coeffs)
                print(list(poldb_encode.filter_poly(coeffs, l)))
            off = w.tell()
            n = poldb_encode.encode_poly(w, coeffs, l)
            print(
                f"{l=} size={w.tell() - off} wrote {n} coefficients",
                file=sys.stderr,
            )
