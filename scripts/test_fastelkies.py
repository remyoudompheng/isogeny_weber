"""
Implementation and validation of fastElkies' algorithm from
https://arxiv.org/pdf/cs/0609020.pdf
"""

from sage.all import *
from sage.schemes.elliptic_curves.ell_curve_isogeny import (
    compute_isogeny_kernel_polynomial,
)
from isogeny_weber import Database
from isogeny_weber import isogenies
from isogeny_weber import ntlext

DEBUG = False


def debug(*args):
    if DEBUG:
        print(*args)


def fastElkies_dbg(E1, E2, l):
    """
    The goal is to compute the power series of the isogeny around the
    point at infinity. If l is odd (always the case for prime l > 2),
    we only need to determine the kernel as the square root of the denominator
    (degree (l-1)/2).

    For this, only 2l coefficients of T, U are needed.
    """
    Rx = PolynomialRing(E1.base_ring(), "x")
    x = Rx.gen()
    # Compute C = 1/(1 + Ax^4 + Bx^6) mod x^(8l-5)
    A, B = E1.a4(), E1.a6()
    C = (1 + A * x**4 + B * x**6).inverse_series_trunc(4 * l)
    # Solve differential equation
    # S'^2 = G(x,S) = (1 + A2 S^4 + B2 S^6) / (1 + Ax^4 + Bx^6)
    # S = x + O(x^2)
    A2, B2 = E2.a4(), E2.a6()
    sprec = 8
    S = x + (A2 - A) / 10 * x**5 + (B2 - B) / 14 * x**7
    debug((C * (1 + A * x**4 + B * x**6)).add_bigoh(30))
    while sprec < 4 * l:
        assert sprec % 2 == 0
        if sprec > 2 * l:
            sprec = 2 * l
        # s1 => s1 + x^k s2
        # 2 s1' s2' - dG/dS(x, s1) s2 = G(x, s1) - s1'2
        s1 = Rx(S).truncate(sprec)
        ds1 = s1.derivative()
        s1pows = s1.add_bigoh(2 * sprec).powers(7)
        GS = C * (1 + A2 * s1pows[4] + B2 * s1pows[6])
        debug("ds1**2", (ds1**2).add_bigoh(2 * sprec))
        debug("GS", GS.add_bigoh(2 * sprec))
        dGS = C * (4 * A2 * s1pows[3] + 6 * B2 * s1pows[5])
        # s2' = (dGS / 2s1') s2 + (G(x, s1) - s1'2) / (2s1')
        denom = (2 * ds1).inverse_series_trunc(2 * sprec)
        a = dGS * denom
        b = (GS - ds1**2) * denom
        debug("b =", b.add_bigoh(2 * sprec))
        s2 = a.solve_linear_de(prec=2 * sprec, b=b, f0=0)
        debug("s2 =", s2)
        debug(s2.derivative())
        debug(a * s2 + b)
        S = s1 + s2
        debug("=======================")
        debug(f"eq prec={2*sprec}")
        debug(2 * ds1 * s2.derivative() - dGS * s2)
        debug(GS - ds1**2)
        debug("new S")
        debug(S)
        sprec = 2 * sprec
    S = S.truncate(4 * l)
    debug("S")
    debug(S.add_bigoh(50))
    debug("RESULT")
    debug((derivative(S) ** 2).add_bigoh(50))
    debug((C * (1 + A2 * S**4 + B2 * S**6)).add_bigoh(50))
    # Reconstruct:
    # S = x * T(x^2)
    # N / D = x / T(1/x)^2
    T = Rx([S[2 * i + 1] for i in range(2 * l)]).add_bigoh(2 * l)
    U = 1 / T**2
    debug(U)
    debug("RATIONAL APPROX")
    _, Q = Rx(U).rational_reconstruction(x ** (2 * l), l, l)
    Q = Q.add_bigoh((l + 1) // 2).sqrt()
    debug(Q)
    ker = Rx(Q).reverse().monic()
    debug(ker)
    assert ker.degree() == (l - 1) // 2
    return ker

def fastElkies_series(E1, E2, l):
    """
    Implementation using power series objects
    """
    Rx, x = E1.base_ring()["x"].objgen()
    # Compute C = 1/(1 + Ax^4 + Bx^6) mod x^4l
    A, B = E1.a4(), E1.a6()
    C = (1 + A * x**4 + B * x**6).inverse_series_trunc(4 * l)
    # Solve differential equation
    # The number of terms doubles at each iteration.
    # S'^2 = G(x,S) = (1 + A2 S^4 + B2 S^6) / (1 + Ax^4 + Bx^6)
    # S = x + O(x^2)
    A2, B2 = E2.a4(), E2.a6()
    S = x + (A2 - A) / 10 * x**5 + (B2 - B) / 14 * x**7
    sprec = 8
    while sprec < 4 * l:
        assert sprec % 2 == 0
        if sprec > 2 * l:
            sprec = 2 * l
        # s1 => s1 + x^k s2
        # 2 s1' s2' - dG/dS(x, s1) s2 = G(x, s1) - s1'2
        s1 = Rx(S).truncate(sprec)
        ds1 = s1.derivative()
        s1pows = s1.add_bigoh(2 * sprec).powers(7)
        GS = C * (1 + A2 * s1pows[4] + B2 * s1pows[6])
        dGS = C * (4 * A2 * s1pows[3] + 6 * B2 * s1pows[5])
        # s2' = (dGS / 2s1') s2 + (G(x, s1) - s1'2) / (2s1')
        denom = (2 * ds1).inverse_series_trunc(2 * sprec)
        a = dGS * denom
        b = (GS - ds1**2) * denom
        s2 = a.solve_linear_de(prec=2 * sprec, b=b, f0=0)
        S = s1 + s2
        sprec = 2 * sprec
    # Reconstruct:
    # S = x * T(x^2)
    # Compute U = 1/T^2
    # Reconstruct N(1/x) / D(1/x) = U
    T = Rx([S[2 * i + 1] for i in range(2 * l)]).add_bigoh(2 * l)
    U = 1 / T**2
    _, Q = Rx(U).rational_reconstruction(x ** (2 * l), l, l)
    Q = Q.add_bigoh((l + 1) // 2).sqrt()
    # Beware, reversing may not give the correct degree.
    ker = Rx(Q / Q[0]).reverse()
    if ker.degree() < (l - 1) // 2:
        ker = ker.shift((l - 1) // 2 - ker.degree())
    return ker.monic()


def fastElkies_polys(E1, E2, l):
    """
    Imolementation of fastElkies using mostly polynomial
    objects (not power series) and NTL functions.
    """

    def mul_trunc(f, g, n):
        if hasattr(f, "ntl_ZZ_pX"):
            if f is g:
                res = ntlext.sqr_trunc(f.ntl_ZZ_pX(), n)
            else:
                res = ntlext.mul_trunc(f.ntl_ZZ_pX(), g.ntl_ZZ_pX(), n)
            return f.parent()(res, construct=True)
        return f._mul_trunc_(g, n)

    def inv_trunc(f, n):
        if hasattr(f, "ntl_ZZ_pX"):
            res = ntlext.inv_trunc(f.ntl_ZZ_pX(), n)
            return f.parent()(res, construct=True)
        return f.inverse_series_trunc(n)

    Rx = PolynomialRing(E1.base_ring(), "x")
    x = Rx.gen()
    # Compute C = 1/(1 + Ax^4 + Bx^6) mod x^(8l-5)
    A, B = E1.a4(), E1.a6()
    C = inv_trunc(1 + A * x**4 + B * x**6, 4 * l)
    # Solve differential equation
    # S'^2 = G(x,S) = (1 + A2 S^4 + B2 S^6) / (1 + Ax^4 + Bx^6)
    # S = x + O(x^2)
    A2, B2 = E2.a4(), E2.a6()
    sprec = 8
    S = x + (A2 - A) / 10 * x**5 + (B2 - B) / 14 * x**7
    while sprec < 4 * l:
        assert sprec % 2 == 0
        if sprec > 2 * l:
            sprec = 2 * l
        # s1 => s1 + x^k s2
        # 2 s1' s2' - dG/dS(x, s1) s2 = G(x, s1) - s1'2
        s1 = S
        ds1 = s1.derivative()
        s1pows = [1, s1]
        while len(s1pows) < 7:
            s1pows.append(mul_trunc(s1, s1pows[-1], 2 * sprec))
        GS = C * (1 + A2 * s1pows[4] + B2 * s1pows[6])
        dGS = C * (4 * A2 * s1pows[3] + 6 * B2 * s1pows[5])
        # s2' = (dGS / 2s1') s2 + (G(x, s1) - s1'2) / (2s1')
        denom = inv_trunc(2 * ds1, 2 * sprec)
        a = mul_trunc(dGS, denom, 2 * sprec)
        b = mul_trunc(GS - ds1**2, denom, 2 * sprec)
        s2 = a.add_bigoh(2 * sprec).solve_linear_de(prec=2 * sprec, b=b, f0=0)
        S = s1 + Rx(s2)
        sprec = 2 * sprec
    # Reconstruct:
    # S = x * T(x^2)
    # N / D = x / T(1/x)^2
    T = Rx([S[2 * i + 1] for i in range(2 * l)])
    U = inv_trunc(mul_trunc(T, T, 2 * l), 2 * l)
    _, Q = U.rational_reconstruction(x ** (2 * l), l, l)
    Q = Q.add_bigoh((l + 1) // 2).sqrt()
    ker = Rx(Q).reverse().monic()
    assert ker.degree() == (l - 1) // 2
    return ker


def test_isogeny(E1, E2, l):
    print("====================")
    print("Field", E1.base_ring())
    print("Degree", l)
    t0 = cputime()
    ker1 = fastElkies_dbg(E1, E2, l)
    print(f"fastElkies' for degree {l} (dt={cputime(t0):.3f}s)")

    t0 = cputime()
    ker1b = fastElkies_series(E1, E2, l)
    print(f"fastElkies' (series) in {cputime(t0):.3f}s")
    assert ker1 == ker1b

    t0 = cputime()
    ker1c = fastElkies_polys(E1, E2, l)
    print(f"fastElkies' (polys) in {cputime(t0):.3f}s")
    assert ker1 == ker1c

    t0 = cputime()
    ker2 = compute_isogeny_kernel_polynomial(E1, E2, l)
    print(f"Stark for degree {l} (dt={cputime(t0):.3f}s)")
    assert ker1 == ker2
    assert E1.isogeny(ker1, codomain=E2, degree=l)


def run_tests():
    global DEBUG
    # Isogeny of degree 97 from Elliptic Curve defined by y^2 = x^3 + 121602776*x + 188664552 over Finite Field of size 277976879 to Elliptic Curve defined by y^2 = x^3 + 214241175*x + 27907112 over Finite Field of size 277976879
    DEBUG = True
    l = 97
    p = 277976879
    E1 = EllipticCurve(GF(p), [121602776, 188664552])
    E2 = EllipticCurve(GF(p), [214241175, 27907112])
    test_isogeny(E1, E2, l)
    DEBUG = False

    l = 457
    p = 59082508900880636655564504693104595868355090311619801145623453915080915481407
    E1 = EllipticCurve(GF(p), [121602776, 188664552])
    A = 3288579942273539662745471167389272889853167238685779289801955464935661036413
    B = 42643982479197598813553327061352754014789261536225922559350357912362046904977
    E2 = EllipticCurve(GF(p), [A, B])
    test_isogeny(E1, E2, l)

    l = 941
    p = next_prime(2**256)
    E1 = EllipticCurve(GF(p), [1234, 567])
    A = 68289133708195951986793415482806693709365846365964095894029896892276020884624
    B = 67002306878265302458306603122827928971374239007364812415569603640764237824697
    E2 = EllipticCurve(GF(p), [A, B])
    test_isogeny(E1, E2, l)

    # Some supersingular curve
    p = 293561446818847499784262243567206202603
    x = polygen(GF(p))
    K = GF((p, 2), names="a", modulus=x**2 + 1)
    i = K.gen()
    # fmt:off
    E1 = EllipticCurve_from_j(268665913341107103624454227343821256366*i + 285098770117101280399385345267921593360)
    A = 72009777730807551475058100194533620717*i+8616118947305132173334473622872245570
    B = 204515145877791226504831010185676465198*i+125417762384496823083602086861458727095
    # fmt:on
    E2 = EllipticCurve(K, [A, B])
    test_isogeny(E1, E2, 257)


def bench(K, l, db):
    while True:
        f = K.random_element()
        wp = db.modular_polynomial(l, base_ring=K, y=f)
        roots, _, _ = isogenies._weber_poly_roots_frobenius(wp, K, f)
        if roots:
            f2, j2 = roots[0]
            break
    # Compute codomain
    wx = db.modular_polynomial(l, base_ring=K, y=f2)
    j = (f**24 - 16) ** 3 / f**24
    E1 = EllipticCurve_from_j(j)
    A, B = E1.a4(), E1.a6()
    phix = wx.derivative()(f) * (3 * (f2**24 - 16) ** 2 - j2) / f2
    phiy = wp.derivative()(f2) * (3 * (f**24 - 16) ** 2 - j) / f
    jj = 18 * B / A * j
    jj2 = K(-phix * jj / (l * phiy))
    mm = jj2 / j2
    kk = jj2 / (1728 - j2)
    E2 = EllipticCurve(K, [l**4 * mm * kk / 48, l**6 * mm**2 * kk / 864])
    assert E2.j_invariant() == j2

    t0 = cputime()
    ker1 = fastElkies_dbg(E1, E2, l)
    print(f"fastElkies' (debug) in {cputime(t0):.3f}s")

    t0 = cputime()
    ker1b = fastElkies_series(E1, E2, l)
    print(f"fastElkies' (series) in {cputime(t0):.3f}s")
    assert ker1 == ker1b

    t0 = cputime()
    ker1c = fastElkies_polys(E1, E2, l)
    print(f"fastElkies' (polys) in {cputime(t0):.3f}s")
    assert ker1 == ker1c

    if l < 80:
        t0 = cputime()
        ker2 = compute_isogeny_kernel_polynomial(E1, E2, l)
        print(f"Sage Stark in {cputime(t0):.3f}s)")
        assert ker1 == ker2

    assert E1.isogeny(ker1, codomain=E2, degree=l)


if __name__ == "__main__":
    import sys

    proof.arithmetic(False)
    run_tests()
    dbname = sys.argv[1]
    db = Database(dbname)
    for bits in range(300, 1500, 100):
        for l in range(100, 2 * bits // 3, 100):
            print(f"Test p with {bits} bits, l={l}")
            K = GF(random_prime(2**bits, lbound=2 ** (bits - 1)))
            bench(K, next_prime(l), db)
