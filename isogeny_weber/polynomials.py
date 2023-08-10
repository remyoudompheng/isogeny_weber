"""
Helper functions for polynomial computations
"""

from sage.all import ZZ, pari
import sys

try:
    from . import ntlext as _ntlext

    print("NTL extensions are available", file=sys.stderr)
except ImportError:
    _ntlext = None
    print("NTL Cython extensions NOT available", file=sys.stderr)


def frobenius_mod(h, p):
    res = _frobenius_mod_ntl(h, p)
    if res is None:
        res = _frobenius_mod_squareshift(h, p)
    return res


def _frobenius_mod_ntl(h, p):
    if _ntlext is not None and hasattr(h, "ntl_ZZ_pX"):
        res = _ntlext.xpow(p, h.ntl_ZZ_pX())
        return h.parent()(res, construct=True)
    return None


def _frobenius_mod_squareshift(h, p):
    """
    Frobenius element in k[x]/h, i.e. x^p mod h

    This naive method is faster than square&multiply.
    NTL/FLINT have dedicated methods not available in Sage.
    """
    res = h.parent()(1)
    for i, d in enumerate(reversed(ZZ(p).digits(32))):
        if i > 0:
            res = pow(res, 32, h)
        res = res.shift(d)
    return res % h


def powmod(f, e, h):
    """
    Modular exponentiation, using NTL with fallback on PARI
    """
    res = powmod_ntl(f, e, h)
    if res is None:
        res_pari = pari.Mod(f._pari_with_name(), h._pari_with_name()) ** e
        res = h.parent()(res_pari.lift())
    return res


def powmod_ntl(f, e, h):
    if _ntlext is not None and hasattr(h, "ntl_ZZ_pX"):
        if f.degree() >= h.degree():
            f = f % h  # NTL needs this
        res = _ntlext.powmod(f.ntl_ZZ_pX(), e, h.ntl_ZZ_pX())
        return h.parent()(res, construct=True)
    return None


def mul_trunc(f, g, n):
    if _ntlext is not None and hasattr(f, "ntl_ZZ_pX"):
        if f is g:
            res = _ntlext.sqr_trunc(f.ntl_ZZ_pX(), n)
        else:
            res = _ntlext.mul_trunc(f.ntl_ZZ_pX(), g.ntl_ZZ_pX(), n)
        return f.parent()(res, construct=True)
    return f._mul_trunc_(n)


def inv_trunc(f, n):
    if _ntlext is not None and hasattr(f, "ntl_ZZ_pX"):
        res = _ntlext.inv_trunc(f.ntl_ZZ_pX(), n)
        return f.parent()(res, construct=True)
    return f.inverse_series_trunc(n)


def modular_composition(f, g, modulus):
    if _ntlext is not None:
        res = _ntlext.compmod(f.ntl_ZZ_pX(), g.ntl_ZZ_pX(), modulus.ntl_ZZ_pX())
        return modulus.parent()(res, construct=True)
    return modular_automorphism(modulus, g)(f)


def modular_automorphism(modulus, xp):
    """
    Assumes that the automorphism group is abelian.

    Returns a function F such that F(g) is actually
    the modular composition g(F)

    xp can be the Frobenius or a scalar multiplication automorphism.
    """
    # If f = sum(fi x^i), f(g) = sum(fi g^i)
    # Brent-Kung method:
    # Writing indices i = at+b the sum becomes:
    # sum(a=0..deg/t, g^at * sum(b=0..t, f[at+b] g^b))
    t = modulus.degree().isqrt() + 1
    smalls = [modulus.parent()(1), xp]
    while len(smalls) < t:
        smalls.append((smalls[-1] * xp) % modulus)
    xpt = (smalls[-1] * xp) % modulus

    def f(pol):
        if pol == 0:
            return pol
        blocks = [
            sum(pol[a + b] * smalls[b] for b in range(t) if a + b <= pol.degree())
            for a in range(0, pol.degree() + 1, t)
        ]
        # Compute sum(blocks[a] xp^at) by Horner rule
        res = blocks[-1]
        for b in reversed(blocks[:-1]):
            res = (res * xpt) % modulus
            res += b
        return res

    return f


def fast_adams_operator(p, k):
    """
    Apply transformation x -> x^k (Graeffe transform) to roots of polynomial
    This is equivalent to p.adams_operator(k), but faster.

    The complexity is quasi-linear w.r.t. degree of p.

    See https://doi.org/10.1016/j.jsc.2005.07.001
    Bostan, Flajolet, Salvy, Schost, Fast computation of special resultants
    """
    d = p.degree()
    assert p.is_monic()
    assert p.base_ring().characteristic() > d
    assert p[0] != 0
    R = p.parent()
    # Build Newton series Sum(sum(root^k) t^k) = dP / P
    newton = p.derivative().reverse() * p.reverse().inverse_series_trunc(k * d + 1)
    # Extract Newton sums where exponent is a multiple of k
    # Reconstruct polynomial using exp(integral dP/P) = P
    f = R([-newton[k * i] for i in range(1, d + 1)])
    # result = f.integral().add_bigoh(d + 1).exp(prec=d + 1)
    # Handmade Newton iteration following section 2.2.1 of BFSS paper
    res = 1 + f[0] * R.gen()
    prec = 2
    while prec <= d:
        # m_ is very small
        m_ = f - res.derivative() * res.inverse_series_trunc(2 * prec)
        m = 1 + m_.truncate(2 * prec).integral()
        res = (res * m).truncate(2 * prec)
        prec = 2 * prec
    result = res.truncate(d + 1).reverse()
    assert result.degree() == d
    return result


def xp_from_cubicp(h, cubic_p, a, b):
    """
    Compute x^p mod h from the knowledge of (x^3+ax+b)^p mod h

    This is section 4.1 in:

    Pierrick Gaudry, François Morain.
    Fast algorithms for computing the eigenvalue in the Schoof-Elkies-Atkin algorithm.
    ISSAC '06: Proceedings of the 2006 international symposium on symbolic and algebraic computation
    Jul 2006, Genoa, Italy, pp.109 - 115, ⟨10.1145/1145768.1145791⟩. ⟨inria-00001009⟩
    https://hal.science/inria-00001009
    """
    R = Poly3Ring(h, a, b, cubic_p)
    g = R.evaly(h)
    z = R.root(g)
    if z is None:
        # should almost never happen
        p = h.parent().characteristic()
        return frobenius_mod(h, p)
    return z % h


class Poly3Ring:
    """
    The ring: (K[x]/h)[y]/(y^3+ay+b-F)
    """

    def __init__(self, h, a, b, F):
        self.Kx = h.parent()
        self.h = h
        self.a = a
        self.b = b
        self.F = F
        self.Fb = F - b

    def add(self, u, v):
        return [uu + vv for uu, vv in zip(u, v)]

    def mulmod(self, f, g):
        return (f * g) % self.h

    def mul(self, u, v):
        # 8 multiplications.
        u0, u1, u2 = u
        v0, v1, v2 = v
        # We need:
        # u0*v0
        # u1*v0+u0*v1 Y
        # u0 v2 + u1 v1 + u2 v0 Y^2
        # u1 v2 + u2 v1 Y^3
        # u2 v2 Y^4
        uv0, uv1, uv2 = u0 * v0, u1 * v1, u2 * v2
        uv01 = (u0 + u1) * (v0 + v1) - uv0 - uv1
        uv02 = (u0 + u2) * (v0 + v2) - uv0 - uv2
        uv12 = (u1 + u2) * (v1 + v2) - uv1 - uv2
        # Y^3 = (F-b) - a Y
        # Y^4 = (F-b)Y - a Y²
        return [
            uv0 + self.mulmod(self.Fb, uv12),
            uv01 - self.a * uv12 + self.mulmod(self.Fb, uv2),
            uv02 + uv1 - self.a * uv2,
        ]

    def shift(self, u):
        # Y^3 = F-aY-b
        # 1 multiplication
        u0, u1, u2 = u
        return [self.mulmod(self.Fb, u2), u0 - self.a * u2, u1]

    def evaly(self, f):
        """
        Compute f(y) in the ring where f has large degree.

        This is similar to Brent-Kung modular composition.

        The cost is:
        * B multiplications in K[x]/h (baby powers)
        * 8l/B multiplications in K[x]/h (Hörner rule)
        * some scalar multiplications

        B + 8l/B is optimal for B = sqrt(8l)
        """
        # print("modulus degree", self.h.degree())
        bs = (8 * self.h.degree()).isqrt() + 1
        assert bs >= 3
        # Baby powers
        ZERO, ONE = self.Kx(0), self.Kx(1)
        ypows = [[ONE, ZERO, ZERO], [ZERO, ONE, ZERO], [ZERO, ZERO, ONE]]
        while len(ypows) < bs:
            ypows.append(self.shift(ypows[-1]))
        ybs = self.shift(ypows[-1])  # Y^bs
        blocks = []
        for a in range(0, f.degree() + 1, bs):
            # Compute sum(f[a+i] Y^i)
            blk = [f[a], f[a + 1], f[a + 2]]
            for i in range(3, bs):
                if a + i > f.degree():
                    break
                for j in range(3):
                    blk[j] += f[a + i] * ypows[i][j]
            blocks.append(blk)
        # print("baby steps", len(ypows), "horner steps", len(blocks))
        # Apply Hörner rule
        res = blocks[-1]
        for b in reversed(blocks[:-1]):
            res = self.mul(res, ybs)
            res = self.add(res, b)
        return res

    def root(self, f):
        # Compute the common root of f(Y) and Y^3+aY+b-F
        # using a GCD computation for variable Y.
        f0, f1, f2 = f
        if f2 == 0 and f1 == 0:
            return None
        if f2 == 0:
            d, f1inv, _ = f1.xgcd(self.h)
            if d != 1:
                return None
            root = -self.mulmod(f0, f1inv)
            if (root**3 + self.a * root + self.b - self.F) % self.h != 0:
                return None
            return root
        # Now f has degree 2.
        # Q = (Y^3 + a Y + b-F) // (f2 Y^2 + f1 Y + f0)
        #   = f2inv (Y - f1 / f2)
        # Q*(f2 Y^2 + f1 Y + f0)
        # = Y^3 + (f0 / f2 - f1^2 / f2^2) Y - f0 f1 / f2^2
        d, f2inv, _ = f[2].xgcd(self.h)
        if d != 1:
            return None
        f2inv2 = self.mulmod(f2inv, f2inv)
        z1 = self.a - self.mulmod(f0, f2inv) + self.mulmod(f1 * f1, f2inv2)
        z0 = self.mulmod(f0 * f1, f2inv2) - self.Fb
        root = -z0 * z1.inverse_mod(self.h)
        if (f2 * root**2 + f1 * root + f0) % self.h != 0:
            return None
        return root % self.h
