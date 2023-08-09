"""
Test/benchmark script for Frobenius computations.

Given a modulus polynomial h with degree < log2(p)
compute x^p mod h from F=(x^3+ax+b)^p mod h
in less than log(p) modular products.

Reference:

Pierrick Gaudry, François Morain.
Fast algorithms for computing the eigenvalue in the Schoof-Elkies-Atkin algorithm.
ISSAC '06: Proceedings of the 2006 international symposium on symbolic and algebraic computation
Jul 2006, Genoa, Italy, pp.109 - 115, ⟨10.1145/1145768.1145791⟩. ⟨inria-00001009⟩
https://hal.science/inria-00001009
"""

from sage.all import GF, random_prime, pari, cputime, ZZ
from isogeny_weber.polynomials import _frobenius_mod_ntl


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
            print("argh")
            return None
        f2inv2 = self.mulmod(f2inv, f2inv)
        z1 = self.a - self.mulmod(f0, f2inv) + self.mulmod(f1 * f1, f2inv2)
        z0 = self.mulmod(f0 * f1, f2inv2) - self.Fb
        root = -z0 * z1.inverse_mod(self.h)
        if (f2 * root**2 + f1 * root + f0) % self.h != 0:
            print("argh2")
            return None
        return root % h


def frobenius(h, p):
    # Compute x^p mod h
    res = h.parent()(1)
    for i, d in enumerate(reversed(ZZ(p).digits(32))):
        if i > 0:
            res = pow(res, 32, h)
        res = res.shift(d)
    return res % h


for psize in range(250, 2000, 250):
    for deg in range(100, 1000, 200):
        if deg > psize:
            break
        print(f"Prime size {psize} bits")
        print(f"Modulus degree = {deg}")

        p = random_prime(2**psize, lbound=2 ** (psize - 1))
        K, Kx = GF(p), GF(p)["x"]
        a, b = K.random_element(), K.random_element()
        h = Kx.random_element(deg)

        # Basic test: if F=0, this is just normal division.
        R = Poly3Ring(h, a, b, Kx(0))
        x = Kx.gen()
        f = Kx.random_element(deg - 1)
        g = f % (x**3 + a * x + b)
        ef = R.evaly(f)
        assert all(ef[i] == g[i] for i in range(3))

        # Application to frobenius
        # F = (x^3+ax+b)^p is known
        # x^p is a common root of h(Y) and Y^3+aY+b = F
        # Compute the gcd w.r.t variable Y of h and Y^3+aY+b-F(x)
        F = pow(x**3 + a * x + b, p, h)

        t0 = cputime()
        xp = pow(x, p, h)
        print(f"Sage x^p mod h computed in {cputime(t0):.3f}s")

        t0 = cputime()
        xp2 = frobenius(h, p)
        print(f"Custom x^p mod h computed in {cputime(t0):.3f}s")
        assert xp == xp2

        t0 = cputime()
        xpN = _frobenius_mod_ntl(h, p)
        print(f"NTL x^p mod h computed in {cputime(t0):.3f}s")
        assert xp == xpN

        t0 = cputime()
        xp_pari = pari.Mod(x._pari_with_name(), h._pari_with_name()) ** p
        print(f"PARI x^p mod h computed in {cputime(t0):.3f}s")
        assert xp == Kx(xp_pari.lift())
        # Fast Frobenius
        t0 = cputime()
        R = Poly3Ring(h, a, b, F)
        g = R.evaly(h)
        z = R.root(g)
        print(f"x^p=h(y) mod h(x),y^3+ax+b-F(x) computed in {cputime(t0):.3f}s")
        assert z is not None
        # assert h(z) % h == 0
        assert (z**3 + a * z + b) % h == F
        assert z == xp
