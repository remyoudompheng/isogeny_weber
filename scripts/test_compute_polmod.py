"""
Computation of Weber modular polynomials by transcendental methods.

Test and benchmark the direct computation of Weber modular
polynomials by numerical evaluation and interpolation.

Reference:
Andreas Enge, Computing modular polynomials in quasi-linear time
Mathematics of Computation 78, 267 (2009) 1809-1824
https://www.ams.org/journals/mcom/2009-78-267/S0025-5718-09-02199-1/
https://arxiv.org/abs/0704.3177
"""

import argparse
import traceback

from sage.all import *
from isogeny_weber import Database

try:
    import isogeny_weber.flintext as flintext
except ImportError:
    flintext = None


DEBUG = False

Zxy = ZZ["x,y"]
CC64 = ComplexField(64)


def weberf(t, zeta):
    """
    The Weber f function.
    If a, t are real numbers:
    - f(it) is real
    - f(a+it) and f(-a+it) are complex conjugates

    zeta: the canonical 48-th root of unity.
    """
    return zeta.conjugate() * ((t + 1) / 2).eta() / t.eta()


def poly(l, s, prec):
    # Evaluate a modular polynomial at f(t=is)
    # The l+1 roots of the modular polynomial Phi(f(t)) are:
    # f(lt) and f(t/l)
    # f((t±a)/l) for a in 1 .. (l-1)/2
    # Note that f(is) is minimal for s=1 (value 2^1/4)
    CC = ComplexField(prec)
    t = CC(0, s)
    zeta = CC.zeta(48)
    ft = weberf(t, zeta).real()
    x = polygen(ft.parent())
    r1 = weberf(l * t, zeta).real()
    r2 = weberf(t / l, zeta).real()
    if DEBUG:
        print(r1)
        print(r2)
    factors = [x**2 - (r1 + r2) * x + r1 * r2]
    for a in range(1, (l + 1) // 2):
        # Roots z and zbar
        z = weberf(CC(48 * a, s) / l, zeta)
        if DEBUG:
            print(z)
        factors.append(x**2 - 2 * x * z.real() + z.norm())
    return ft, prod(factors)


def poly_flint(l, s, prec):
    """
    Evaluate a modular polynomial at f(t=is) using FLINT ARB.
    Sage doesn't interface real polynomials, we use complex ones.
    """
    CC = ComplexBallField(prec)
    zeta = CC(ComplexField(prec).zeta(48).conjugate())

    def weberf(t):
        return zeta * ((t + 1) / 2).modular_eta() / t.modular_eta()

    t = CC(0, s)
    ft = weberf(t).real()
    r1 = weberf(l * t).real()
    r2 = weberf(t / l).real()
    cs = [weberf(CC(48 * a, s) / l) for a in range(1, (l + 1) // 2)]
    poly = flintext.rx_from_roots([r1, r2], cs)
    return ft, poly


def test23():
    """
    Test computation for l=23.
    For each power of X, only one coefficient must be found.
    """
    l = 23
    z1, poly1 = poly(l, 1, 2 * l)
    print(f"### {l =}")
    print("Evaluated polynomial at", float(z1))
    pol = {}
    for a in range(1, l + 1):
        c = poly1[a]
        bs = [_b for _b in range(1, l + 1) if (l * a + _b) % 24 == (l + 1) % 24]
        assert len(bs) == 1
        b = bs[0]
        c /= z1**b
        if (a, b) == (l, l):
            assert c.round() == -1
        elif (a, b) == (1, 1):
            cabs = c.round().abs()
            assert cabs & (cabs - 1) == 0
        else:
            assert abs(c - l * (c.round() // l)) < 1e-3, c
        # print(a, b, c)
        pol[(a, b)] = ZZ(c.round())
    print(Zxy(pol))


def test47():
    """
    Test computation for l=47.
    For each power of X, at most 2 coefficients must be found
    """
    l = 47
    z1, poly1 = poly(l, 1, 2 * l)
    z2, poly2 = poly(l, 1.1, 2 * l)
    print(f"### {l =}")
    print(f"Evaluated at {float(z1)} {float(z2)}")
    # print(poly1.change_ring(CC64))
    # print(poly2.change_ring(CC64))
    pol = {}

    def setc(a, b, c):
        if (a, b) == (l, l):
            assert c.round() == -1
        elif (a, b) == (1, 1):
            cabs = c.round().abs()
            assert cabs & (cabs - 1) == 0
        else:
            assert abs(c - l * (c.round() // l)) < 1e-3, c
        c = ZZ(c.round())
        pol[(a, b)] = c
        pol[(b, a)] = c

    for a in range(1, l + 1):
        bs = [_b for _b in range(1, l + 1) if (l * a + _b) % 24 == (l + 1) % 24]
        # print(f"{a=} {bs=}")
        if len(bs) == 2:
            c1 = poly1[a] / z1 ** bs[0]
            c2 = poly2[a] / z2 ** bs[0]
            # interpolate linearly
            p1 = (c2 - c1) / (z2**24 - z1**24)
            p0 = c1 - p1 * z1**24
            setc(a, bs[0], p0)
            setc(a, bs[1], p1)
        else:
            b = bs[0]
            c1 = poly1[a]
            setc(a, b, c1 / z1**b)
    print(Zxy(pol))


def needed_precision(l):
    """
    Experimentally, the largest coefficients has about l bits:
    Some polynomials have higher precision requirements:

    # l=167 needs more than 190 bits
    # l=241 needs more than 280 bits
    # l=251 needs more than 300 bits
    # l=313 needs more than 380 bits
    # l=383 needs more than 460 bits

    >>> needed_precision(563) >= 660
    True
    >>> needed_precision(733) >= 900
    True
    >>> needed_precision(877) >= 1090
    True
    >>> needed_precision(997) >= 1270
    True
    >>> needed_precision(1151) >= 1500
    True
    """
    return 16 + l + l * (l.bit_length() + 1) // 40


def needed_precision_flint(l):
    """
    Modular forms are more precise in FLINT.
    But fast interpolation is not very precise, we need more bits.

    >>> needed_precision_flint(673) >= 860
    True
    >>> needed_precision_flint(719) >= 930
    True
    >>> needed_precision_flint(743) >= 975
    True
    >>> needed_precision_flint(1151) >= 1590
    True
    >>> needed_precision_flint(1297) >= 1790
    True
    """
    return 32 + l + l * (l.bit_length() + 4) // 40


def modpoly_from_complex(l, flint=False):
    """
    Compute from complex numbers with high precision.
    Quadratic algorithm using unoptimized interpolation.
    """
    n_points = l // 24 + 1
    # We need k+1 points if 24k+1 < l
    zs, polys = [], []
    prec = needed_precision(l)
    if flint:
        prec = needed_precision_flint(l)
    for i in range(n_points):
        if flint:
            z, pol = poly_flint(l, 1 + QQ(i) / QQ(n_points), prec)
        else:
            z, pol = poly(l, 1 + QQ(i) / QQ(n_points), prec)
        zs.append(z)
        polys.append(pol)
    print(f"### {l =}")
    print(f"Evaluated at {n_points} points {float(zs[0]):.9f}...{float(zs[-1]):.9f}")
    print(zs[0].parent())
    # print(poly1.change_ring(CC64))
    # print(poly2.change_ring(CC64))
    pol = {}
    pol[(l + 1, 0)] = 1
    pol[(0, l + 1)] = 1
    maxerr = 0.0

    R = RealField(prec)

    def setc(a, b, c):
        c = R(c)
        nonlocal maxerr
        if (a, b) == (l, l):
            cz = c.round()
            assert cz == -1
        elif (a, b) == (1, 1):
            cz = c.round()
            assert cz.abs() & (cz.abs() - 1) == 0
        else:
            cz = l * (c / l).round()
            err = abs(c - cz)
            maxerr = max(maxerr, float(err))
            assert err < 0.1 * l, f"{l=} deg={a},{b} err={float(err)} {c=}"

        pol[(a, b)] = ZZ(cz)
        pol[(b, a)] = ZZ(cz)

    RRx = polys[0].parent()
    z24s = [z**24 for z in zs]
    for a in range((l + 1) // 2, l + 1):
        bs = [_b for _b in range(1, l + 1) if (l * a + _b) % 24 == (l + 1) % 24]
        if not bs:
            continue
        # Solve
        # sum(bs[i] * zs^(24i+j)) = c
        if flint and flintext:
            lag = flintext.rx_interpolate(
                z24s, [(pol[a] / z ** bs[0]) for z, pol in zip(zs, polys)]
            )
        else:
            lag = RRx.lagrange_polynomial(
                [(z24, pol[a] / z ** bs[0]) for z, z24, pol in zip(zs, z24s, polys)]
            )
        for i, b in enumerate(bs):
            if a + b >= l + 1:
                setc(a, b, lag[i])
    # Complete symmetry
    sgn = legendre_symbol(2, l)
    s = gcd(12, (l - 1) // 2)
    for dx, dy in list(pol):
        if dx <= l and dy <= l and dx + dy > l + 1:
            dxl, dyl = l + 1 - dx, l + 1 - dy
            shift = dx + dy - (l + 1)
            b = shift // (2 * s)
            pol[(dxl, dyl)] = ((sgn ** (b % 2)) << (b * s)) * pol[(dx, dy)]
    print("max error", maxerr)
    return Zxy(pol)


def main():
    argp = argparse.ArgumentParser()
    argp.add_argument("--pari", action="store_true")
    argp.add_argument(
        "REFDB", nargs="?", help="Reference Weber modular polynomial database"
    )
    args = argp.parse_args()

    db = Database(args.REFDB)

    for l in sorted(db.keys()):
        if flintext is None:
            t = cputime()
            pp = modpoly_from_complex(l)
            print(f"Computed modular polynomial {l=} in {cputime(t):.3}s")
        else:
            t = cputime()
            try:
                pp = modpoly_from_complex(l, flint=True)
            except Exception as e:
                traceback.print_exc()
                continue
        print(f"Computed modular polynomial {l=} in {cputime(t):.3}s (FLINT)")
        # Compare with reference
        pm = Zxy(db[l])
        assert pp == pm
        # Compare with pari
        if args.pari:
            t = cputime()
            ppari = pari.polmodular(l, 1)
            print(f"PARI in {cputime(t):.3}s")
            assert pp == Zxy(ppari)


if __name__ == "__main__":
    t = cputime()
    test23()
    print("modular polynomial l=23", cputime(t))

    t = cputime()
    test47()
    print("modular polynomial l=47", cputime(t))

    main()
