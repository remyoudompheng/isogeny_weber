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


def compute_modular_polynomial(l, base_ring=None):
    """
    Compute a modular polynomial as a bivariate polynomial,
    optionally using a specific coefficient ring.

    Bivariate polynomials may be suboptimal for certain uses.
    """
    from sage.rings.all import IntegerRing, PolynomialRing

    R = IntegerRing() if base_ring is None else base_ring
    coeffs = weber_modular_poly_coeffs(l)
    # Complete symmetry
    sgn = legendre_symbol(2, l)
    s = gcd(12, (l - 1) // 2)
    for dx, dy in list(coeffs):
        if dx >= dy and dx <= l and dy <= l and dx + dy > l + 1:
            dxl, dyl = l + 1 - dx, l + 1 - dy
            shift = dx + dy - (l + 1)
            b = shift // (2 * s)
            coef = ((sgn ** (b % 2)) << (b * s)) * coeffs[(dx, dy)]
            # Use the same object to share memory
            coeffs[(dxl, dyl)] = coef
            coeffs[(dyl, dxl)] = coef

    Rxy = PolynomialRing(R, 2, "x,y")
    return Rxy(coeffs)

def instantiate_modular_polynomial(l, x):
    """
    Returns the Weber modular polynomial of level l and its 2 partial
    derivatives, instantiated using x for the first variable,
    as univariate polynomials over the parent ring of x.
    """
    R = x.parent()
    Rx = R["x"]
    plist = [R(0) for _ in range(l + 2)]
    plistx = [R(0) for _ in range(l + 2)]
    plisty = [R(0) for _ in range(l + 2)]
    powers = R(x).powers(l + 2)
    coeffs = weber_modular_poly_coeffs(l)

    sgn = legendre_symbol(2, l)
    s = gcd(12, (l - 1) // 2)

    for (dx, dy), a in coeffs.items():
        plist[dx] += a * powers[dy]
        if dx > 0:
            plistx[dx - 1] += (a * dx) * powers[dy]
        if dy > 0:
            plisty[dx] += (a * dy) * powers[dy - 1]
        # Apply symmetry Phi(2^1/4 x, 2^1/4 y) has doubly symmetric coefficients
        if dx <= l and dy <= l and dx + dy > l + 1:
            dxl, dyl = l + 1 - dx, l + 1 - dy
            shift = dx + dy - (l + 1)
            b = shift // (2 * s)
            al = ((sgn ** (b % 2)) << (b * s)) * coeffs[(dx, dy)]
            plist[dxl] += al * powers[dyl]
            if dxl > 0:
                plistx[dxl - 1] += (a * dxl) * powers[dyl]
            if dyl > 0:
                plisty[dxl] += (a * dyl) * powers[dyl - 1]

    return Rx(plist), Rx(plistx), Rx(plisty)

def weber_modular_poly_coeffs(l):
    """
    Return a dictionary of coefficients for the Weber modular
    polynomial of level l.

    This dictionary omits coefficients with total degree less than (l+1)//2
    """
    prec = required_precision(l)
    while True:
        try:
            return _weber_modular_poly_coeffs(l, prec)
        except PrecisionError as err:
            # This should not happen at all but would require
            # adjusting the precision for an actual fix.
            import math
            import sys
            import traceback

            traceback.print_exc()
            print(f"PrecisionError: {err.message}", file=sys.stderr)
            _, b = math.frexp(err.error)
            # Retry with 32-256 additional bits
            add = max(32, min(256, 2 * b))
            print(f"Retrying with additional {add} bits", file=sys.stderr)
            prec += add


class PrecisionError(Exception):
    def __init__(self, error, message):
        self.error = error
        self.message = message


def _weber_modular_poly_coeffs(l, prec):
    """
    Compute the Weber modular polynomial of level l.

    The memory storage requirement is:
      ~l²/48 real numbers at precision l
      ~l²/96 integers of size l
    so usually only suitable for l < 10000
    """
    eval_points = l // 48 + 1
    R = RealField(prec)
    # We need k+1 points if 24k+1 < l
    # To improve numerical stability we want the values of Weber to be
    # regularly spaced: since we choose them close to the extremum
    # the argument should be 1 + sqrt(kε)
    zs, polys = [], []
    for i in range(eval_points):
        z, pol = eval_modular_numerical(l, 1 + (R(i + 1) / R(10 * eval_points)).sqrt(), prec)
        zs.append(z)
        polys.append(pol)
    verbose(
        f"Evaluated Φ[{l}] ({prec=}) at {eval_points} points {float(zs[0]):.9f}...{float(zs[-1]):.9f}",
        level=2,
    )
    pol = {}
    pol[(l + 1, 0)] = ZZ(1)
    pol[(0, l + 1)] = ZZ(1)

    RB = zs[0].parent()

    def setc(a, b, cc):
        c = R(cc)
        if (a, b) == (l, l):
            cz = c.round()
            assert cz == -1
        elif (a, b) == (1, 1):
            cz = c.round()
            assert cz.abs() & (cz.abs() - 1) == 0
        else:
            if cc.diameter() > 0.1 * l:
                raise PrecisionError(cc.diameter(), f"{l=} deg={a},{b} err={cc.diameter()} {c=}")
            # Kronecker congruence: coefficients are multiples of l.
            cz = l * (c / l).round()
        cz = ZZ(cz)
        pol[(a, b)] = cz
        pol[(b, a)] = cz

    sgn = legendre_symbol(2, l)
    s = gcd(12, (l - 1) // 2)
    # We only iterate on degrees <= (l+1)/2 because we can fill
    # half of coefficients using the degree symmetry.
    # We use the degree symmetry to "duplicate" evaluation data.
    z24s = [z**24 for z in zs]
    for a in range(1, (l + 1) // 2 + 1):
        # Exponents of y are b0, b0+24, etc.
        # The coefficient of x^a is sum(cj y^(b0+24j)) = y^b0 P(y^24)
        b0 = (l + 1 - l * a) % 24
        bs = [_b for _b in range(b0, l + 1, 24)]
        if not bs:
            continue
        # The coefficient of x^(l+1-a) is y^(l+1-b0) Q(1/y^24)
        # where P and Q are related by P(2^12 x) = pm 2^K Q(x)
        shift = l + 1 - (a + b0)
        bb = shift // (2 * s)
        # Gather values of Q from degree l+1-a
        xs = [1 / z for z in z24s]
        ys = [cpol[l + 1 - a] / z ** (l + 1 - b0) for z, cpol in zip(zs, polys)]
        # Gather values of Q from degree a
        if len(xs) < len(bs):
            # Q(z^24/2^12) = coeff[a] / z^b0 / pm 2^K
            const = 1 / RB(sgn ** (a % 2) * 2 ** (bb * s))
            xs += [z / 4096 for z in z24s]
            ys += [const * cpol[a] / z**b0 for z, cpol in zip(zs, polys)]
        if len(xs) > len(bs):
            xs = xs[: len(bs)]
            ys = ys[: len(bs)]
        assert len(xs) == len(bs)
        interp = real_poly_interpolate(xs, ys, algorithm="newton")
        if a == (l + 1) // 2:
            eps = interp[len(bs) // 2].diameter()
            _, _m, _e = eps.sign_mantissa_exponent()
            eff_prec = -(_e + _m.bit_length())
            verbose(f"final extra precision {eff_prec} bits ({eps})", level=2)
        for i, b in enumerate(bs):
            if a + b <= l + 1:
                setc(l + 1 - a, l + 1 - b, interp[i])
        # Free memory
        for cpol in polys:
            cpol[a], cpol[l + 1 - a] = None, None
    return pol


def eval_modular_numerical(l, s, prec):
    """
    Evaluate a modular polynomial at ft=f(t=is) using floating-point
    complex numbers.

    Returns a monic polynomial of degree l+1
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
    return ft, poly.list()


def required_precision(l):
    """
    Modular forms are very precise in FLINT.
    But interpolation is not numerically stable.

    The following bounds were determined experimentally
    by running the computation for l < 5000
    using FLINT-ARB 2.23 `arb_poly_interpolate_newton`

    Some values of l require more precision than their neighbours:

    >>> required_precision(229) >= 310
    True
    >>> required_precision(379) >= 500
    True
    >>> required_precision(599) >= 800
    True
    >>> required_precision(743) >= 1000
    True
    >>> required_precision(769) >= 1050
    True
    >>> required_precision(1151) >= 1650
    True
    >>> required_precision(1297) >= 1850
    True
    >>> required_precision(1439) >= 2050
    True
    >>> required_precision(1657) >= 2300
    True
    >>> required_precision(2221) >= 3180
    True
    >>> required_precision(2377) >= 3400
    True
    >>> required_precision(2617) >= 3750
    True
    >>> required_precision(2833) >= 4140
    True
    >>> required_precision(2999) >= 4300
    True
    >>> required_precision(3169) >= 4500
    True
    """
    return 32 + int(l * 1.4) + l * l.bit_length() // 200
