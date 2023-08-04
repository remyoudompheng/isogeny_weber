"""
Compute Schläfli modular equations for the Weber function.

William B. Hart, A Guide to Theta Functions and Weber's Modular Equations
http://homepages.warwick.ac.uk/~masfaw/Chapter4.pdf

Andreas Enge, Computing Modular Polynomials in quasi-linear time
https://arxiv.org/pdf/0704.3177.pdf
"""

import argparse
import io

from sage.all import *
from isogeny_weber import Database

R = PolynomialRing(ZZ, "x,y")
Rab = PolynomialRing(ZZ, "A,B", order="lex")


@cached_function
def chebyshev(n):
    x = polygen(QQ)
    return (2 * chebyshev_T(n, x / 2)).change_ring(ZZ)


def schlafli(Phi, l):
    P = Phi
    r = gcd(12, (l + 1) // 2)
    s = gcd(12, (l - 1) // 2)

    x, y = R.gens()
    Ahom = x ** (2 * r) + y ** (2 * r)
    Bhom = (x * y) ** (2 * s) + legendre_symbol(2, l) * 2**s
    Ahom_powers = Ahom.powers((l + 1) // (2 * r) + 1)
    Bhom_powers = Bhom.powers((l - 1) // (2 * s) + 1)

    def evalAB(pab):
        return sum(
            Ahom_powers[da]
            * Bhom_powers[db]
            * (c * (x * y) ** ((l + 1) // 2 - da * r - db * s))
            for (da, db), c in pab.iterator_exp_coeff()
        )

    # Like evalAB but for B^b P(a)
    def evalABterm(expb, pa):
        return Bhom_powers[expb] * sum(
            Ahom_powers[da] * (c * (x * y) ** ((l + 1) // 2 - da * r - expb * s))
            for da, c in pa.dict().items()
        )

    F = Rab(0)
    Asym, Bsym = Rab.gens()
    # Handle monic term x^(l+1) + y^(l+1)
    F += chebyshev((l + 1) // (2 * r))(Asym)
    P -= x ** (l + 1) + y ** (l + 1)
    # Replace P by a dictionary of homogeneous components
    homs = P.homogeneous_components()
    del P

    layers = (2 * l) // (2 * s) + 1
    bmax = (layers + 1) // 2
    for b in range(bmax):
        # B^(bmax-b) corresponds to the homogeneous component
        # of total degree 2l - 2bs (maximal degree 2l)
        # and degmin + 2bs
        deg = 2 * l - 2 * b * s
        terma = 0 * chebyshev(1)
        if deg not in homs:
            continue
        for (dx, dy), c in homs[deg].iterator_exp_coeff():
            if dx < dy:
                continue
            if dx == l + 1:
                continue
            a = (dx - deg // 2) // r
            assert (dx, dy) == (deg // 2 + a * r, deg // 2 - a * r)
            if a == 0:
                terma += c
            else:
                terma += c * chebyshev(a)
        fterm = Bsym ** (bmax - 1 - b) * terma(Asym)
        Pterm = evalABterm(bmax - 1 - b, terma)
        F += fterm
        for _d, _t in Pterm.homogeneous_components().items():
            homs[_d] -= _t

    # In traditional notation:
    # A = (x/y)^r + (y/x)^r has total degree 0
    # B = (xy)^s + legendre_symbol(2, l) * 2**s / (xy)^s
    # Phi = (xy)^(l+1)/2 * F(A,B)
    assert all(h == 0 for h in homs.values())
    return F


def main():
    argp = argparse.ArgumentParser()
    argp.add_argument("--limit", default=None, type=int, help="only process l <= limit")
    argp.add_argument("INPUT_DB")
    args = argp.parse_args()
    db = Database(args.INPUT_DB)

    for l in sorted(db.keys()):
        if args.limit and l > args.limit:
            continue
        # Usually there are about l^2/24 coefficients in Phi
        Phi = db[l]
        Phicoeffs = Phi.coefficients()
        Phisize = sum(_c.bit_length() for _c in Phicoeffs)
        print(f"Phi[{l}] = {len(Phicoeffs)} coefficients, total size {Phisize} bits")
        F = schlafli(Phi, l)
        # Usually there are about l^2/96 coefficients in F
        fcoeffs = F.coefficients()
        fsize = sum(_c.bit_length() for _c in fcoeffs)
        print(f"Modular equation: {len(fcoeffs)} coefficients ({fsize} bits)")
        if l < 32:
            print(F)


if __name__ == "__main__":
    main()
