"""
Generation utility for the Weber modular polynomial database.

This utility does not read input files and computes
all polynomials as needed.

A few minutes are enough to generate all polynomials for prime l < 1000.
About one hour is needed to generate all polynomials for prime l < 2000.
"""

import argparse
import io
import sys
import time
import traceback

from sage.all import primes, parallel, set_verbose
from isogeny_weber import poldb_encode
from isogeny_weber.poldb_compute import weber_modular_poly_coeffs


def compute_encode(l):
    try:
        cs = weber_modular_poly_coeffs(l)
    except Exception:
        traceback.print_exc()
        return b"", -1
    cl = [(a, b, c) for (a, b), c in cs.items()]
    w = io.BytesIO()
    n = poldb_encode.encode_poly(w, cl, l)
    return w.getvalue(), n


def parallel_compute(ls, threads=1):
    if threads == 1:
        for l in ls:
            blob, n = compute_encode(l)
            yield l, blob, n
    else:
        idx = 0
        res = {}
        for (args, _), result in parallel(threads)(compute_encode)(ls):
            ll = args[0]
            res[ll] = result
            while idx < len(ls) and (nextl := ls[idx]) in res:
                blob, n = res[nextl]
                yield nextl, blob, n
                idx += 1
            if idx == len(ls):
                return


if __name__ == "__main__":
    argp = argparse.ArgumentParser()
    argp.add_argument("--min", default=5, type=int)
    argp.add_argument("-t", default=1, type=int, help="Number of threads")
    argp.add_argument("-v", action="count")
    argp.add_argument("OUTPUT")
    argp.add_argument("MAXPRIME", type=int)
    args = argp.parse_args()

    t0 = time.time()
    set_verbose(args.v)
    with open(args.OUTPUT, "wb") as w:
        ls = list(primes(args.min, args.MAXPRIME + 1))
        for l, encpoly, n in parallel_compute(ls, args.t):
            w.write(encpoly)
            elapsed = time.time() - t0
            print(
                f"t={elapsed:.1f}s {l=} size={len(encpoly)} wrote {n} coefficients",
                file=sys.stderr,
            )
