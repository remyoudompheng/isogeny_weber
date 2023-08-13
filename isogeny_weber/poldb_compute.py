"""
On-the-fly computation of Weber modular polynomials.

This library does not use isogeny volcanoes but transcendantal
methods using evaluation/interpolation of floating-point
polynomials.

When available, evaluation of η and fast polynomial interpolation
from FLINT are used.

The complexity is roughly O(l^3 log(l)^?) which is quasi-linear
in the size of the polynomial.

When FLINT library is enabled, this is usually 2x-3x faster than
equivalent PARI function polmodular(l, 1)

Evaluating the full polynomial for l=2493 should take a couple of minutes.
Evaluating the full polynomial for l=4999 should take less than 1hr.

Reference:
Andreas Enge, Computing modular polynomials in quasi-linear time
Mathematics of Computation 78, 267 (2009) 1809-1824
https://www.ams.org/journals/mcom/2009-78-267/S0025-5718-09-02199-1/
https://arxiv.org/abs/0704.3177
"""

from sage.all import (
    ZZ,
    QQ,
    RealField,
    ComplexField,
    ComplexBallField,
    legendre_symbol,
    gcd,
)
from sage.misc.verbose import verbose

from .polynomials import real_poly_from_roots, real_poly_interpolate

def compute_modular_polynomial(l, base_ring=None, y=None, coeffs=None):
    """
    Returns the Weber modular polynomial of level l
    as a Sage ring element, optionally specialized for a given coefficient ring
    or for a numerical value of the y variable.

    coeffs: a dictionary returned by weber_modular_poly_coeffs
    """
    from sage.rings.all import IntegerRing, PolynomialRing

    R = IntegerRing() if base_ring is None else base_ring
    if coeffs is None:
        coeffs = weber_modular_poly_coeffs(l)
    if y is None:
        # Bivariate
        Rxy = PolynomialRing(R, 2, "x,y")
        return Rxy(coeffs)
    else:
        # Univariate
        Rx = PolynomialRing(R, "x")
        plist = [R(0) for _ in range(l + 2)]
        powers = R(y).powers(l + 2)
        for (dx, dy), a in coeffs.items():
            plist[dx] += a * powers[dy]
        return Rx(plist)


def weber_modular_poly_coeffs(l):
    """
    Return a dictionary of coefficients for the Weber modular
    polynomial of level l.

    Note: the dictionary only contains keys such that degx >= degy.
    """
    eval_points = l // 24 + 1
    # We need k+1 points if 24k+1 < l
    zs, polys = [], []
    prec = needed_precision(l)
    for i in range(eval_points):
        z, pol = eval_modular_numerical(l, 1 + QQ(i) / QQ(eval_points), prec)
        zs.append(z)
        polys.append(pol)
    verbose(
        f"Evaluated Φ[l] ({prec=}) at {eval_points} points {float(zs[0]):.9f}...{float(zs[-1]):.9f}",
        level=2,
    )
    pol = {}
    pol[(l + 1, 0)] = ZZ(1)
    pol[(0, l + 1)] = ZZ(1)

    R = RealField(prec)

    def setc(a, b, c):
        c = R(c)
        if (a, b) == (l, l):
            cz = c.round()
            assert cz == -1
        elif (a, b) == (1, 1):
            cz = c.round()
            assert cz.abs() & (cz.abs() - 1) == 0
        else:
            # Kronecker congruence: coefficients are multiples of l.
            cz = l * (c / l).round()
            err = abs(c - cz)
            assert err < 0.1 * l, f"{l=} deg={a},{b} err={float(err)} {c=}"
        cz = ZZ(cz)
        pol[(a, b)] = cz
        pol[(b, a)] = cz

    # We only iterate on degrees >= (l+1)/2 because we can fill
    # half of coefficients using the degree symmetry.
    # We still have 2x "too much" data because of the X,Y symmetry.
    z24s = [z**24 for z in zs]
    for a in range((l + 1) // 2, l + 1):
        bs = [_b for _b in range(1, l + 1) if (l * a + _b) % 24 == (l + 1) % 24]
        if not bs:
            continue
        # Solve
        # sum(bs[i] * z^(24i+j)) = c
        interp = real_poly_interpolate(
            z24s, [(pol[a] / z ** bs[0]) for z, pol in zip(zs, polys)]
        )
        for i, b in enumerate(bs):
            if a + b >= l + 1:
                setc(a, b, interp[i])
    # Complete symmetry
    sgn = legendre_symbol(2, l)
    s = gcd(12, (l - 1) // 2)
    for dx, dy in list(pol):
        if dx >= dy and dx <= l and dy <= l and dx + dy > l + 1:
            dxl, dyl = l + 1 - dx, l + 1 - dy
            shift = dx + dy - (l + 1)
            b = shift // (2 * s)
            coef = ((sgn ** (b % 2)) << (b * s)) * pol[(dx, dy)]
            # Use the same object to share memory
            pol[(dxl, dyl)] = coef
            pol[(dyl, dxl)] = coef
    return pol


def eval_modular_numerical(l, s, prec):
    """
    Evaluate a modular polynomial at ft=f(t=is) using floating-point
    complex numbers.
    """
    CC = ComplexBallField(prec)
    zeta = CC(ComplexField(prec).zeta(48).conjugate())

    def weberf(t):
        return zeta * ((t + 1) / 2).modular_eta() / t.modular_eta()

    t = CC(0, s)
    ft = weberf(t).real()
    # Lattice <1,t> is isogenous to <1,lt> and <1,t/l>
    # but also <l, t+48a> for a in 1..l (taking level 48 structure into account)
    r1 = weberf(l * t).real()
    r2 = weberf(t / l).real()
    cs = [weberf(CC(48 * a, s) / l) for a in range(1, (l + 1) // 2)]
    poly = real_poly_from_roots([r1, r2], cs)
    return ft, poly


def needed_precision(l):
    """
    Modular forms are very precise in FLINT.
    But fast interpolation is not very precise, we need more bits.

    >>> needed_precision(673) >= 860
    True
    >>> needed_precision(719) >= 930
    True
    >>> needed_precision(743) >= 975
    True
    >>> needed_precision(1151) >= 1590
    True
    >>> needed_precision(1297) >= 1800
    True
    >>> needed_precision(1511) >= 2120
    True
    >>> needed_precision(1609) >= 2250
    True
    >>> needed_precision(2593) >= 3740
    True
    """
    return 32 + l + l // 7 + l * l.bit_length() // 40
