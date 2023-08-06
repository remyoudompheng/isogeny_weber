"""
Compute isogenies of a given prime degree l using Weber modular
polynomials.
"""

from sage.all import ZZ, EllipticCurve, polygen, cputime
from sage.misc.verbose import verbose

from .poldb import Database


def isogenies_prime_degree_weber(E, l, weber_db=Database(), only_j=False, check=True):
    """
    Returns an iterator over outgoing isogenies of degree l
    with domain E.

    l must be a prime level in the Weber modular polynomial
    database (usually l < 1000).
    """
    if not ZZ(l).is_prime():
        raise ValueError(f"degree {l} is not prime")
    K = E.base_ring()
    if not K.is_field() or not K.is_finite():
        raise ValueError(f"Base ring {K} is not a finite field")
    j = E.j_invariant()
    if not only_j and (j == K(0) or j == K(1728)):
        raise ValueError(f"j-invariant must not be 0 or 1728")
    if K.characteristic() <= 4 * l:
        raise ValueError(f"Characteristic is too small (needs char K > 4l)")

    A, B = E.a4(), E.a6()
    x = polygen(K)
    eqf = (x**24 - 16) ** 3 - j * x**24
    eqf2 = min((_f for _f, _ in eqf.factor()), key=lambda _f: _f.degree())
    Kext = eqf2.splitting_field("f")
    f = None
    for r, _ in _fast_pari_roots(((x - 16) ** 3 - j * x).change_ring(Kext)):
        try:
            f = r.nth_root(24)
        except ValueError:
            continue
    assert f is not None and eqf(f) == 0
    verbose(f"domain j={j}")
    verbose(f"f-invariant in field {Kext}")
    wp = weber_db.modular_polynomial(l, base_ring=Kext, y=f)
    t0 = cputime()
    roots = list(_weber_poly_roots(wp, K, f, j))
    verbose(f"{len(roots)} roots for modular equation of degree {wp.degree()}", t=t0)
    for f2, j2, mult in roots:
        f2_24 = f2**24
        if j2 not in K:
            continue
        verbose(f"codomain j={K(j2)}")
        if only_j:
            for _ in range(mult):
                yield j2
        else:
            if j2 == 0 or j2 == 1728 or mult > 1:
                raise ValueError(f"Target j-invariant must not be 0 or 1728")
            # Compute equation of normalized codomain and apply Stark algorithm
            # Sutherland, On the evaluation of modular polynomials, section 3.8
            # https://arxiv.org/pdf/1202.3985.pdf
            #
            # The derivative j'(f)/j(f) = 3 * 24 f^23 / (f^24 - 16) - 24 / f
            # f j'(f) = 72 (f^24 - 16)^2 - 24 j(g)
            wx = weber_db.modular_polynomial(l, base_ring=Kext, y=f2)
            phix = wx.derivative()(f) * (3 * (f2_24 - 16) ** 2 - j2) / f2
            phiy = wp.derivative()(f2) * (3 * (f**24 - 16) ** 2 - j) / f
            jj = 18 * B / A * j
            jj2 = K(-phix * jj / (l * phiy))
            mm = jj2 / j2
            kk = jj2 / (1728 - j2)
            E2 = EllipticCurve(K, [l**4 * mm * kk / 48, l**6 * mm**2 * kk / 864])
            assert E2.j_invariant() == j2
            t0 = cputime()
            ker = _fast_elkies(E, E2, l)
            assert ker.degree() == (l - 1) // 2, f"{l=} kernel degree {ker.degree()}\nE1: {E}\nE2: {E2}"
            verbose(f"computed normalized isogeny of degree {l}", t=t0)
            yield E.isogeny(ker, codomain=E2, degree=l, check=check)


_DEBUG = False


def _weber_poly_roots(wpoly, Kbase, f, j):
    """
    Compute roots of the Weber modular polynomial Wl(f, x)
    and iterates over (f2, j2, multiplicity)
    """
    # Use built-in root solving if already working on the base field
    # or if extension field is small.
    if f in Kbase or f.parent().order().bit_length() < 256:
        for r, mult in _fast_pari_roots(wpoly):
            yield r, (r**24 - 16) ** 3 / r**24, mult
        return
    # We want to avoid computing roots over large extension
    # fields, so we will project the polynomial to a small field extension.
    # Because l-isogenies preserve Galois properties, all roots of
    # Wl(f,x) will be in the same tower of extensions as f.

    # If we apply the full transformation to roots, we will obtain the
    # equation for the j-invariant, which can also be obtained using
    # classical modular polynomials.

    # First determine the path to base field:
    # f -> f^k -> optional (x-16)^3-jx
    Kf, f24 = f.parent(), f**24
    if f24 in Kbase:
        K24 = Kbase
        power = next(i for i in (1, 2, 3, 4, 6, 8, 12, 24) if (f**i) in Kbase)
    else:
        # This is only possible if (X-16)^3-jX is irreducible.
        extdeg = Kf.degree() // Kbase.degree()
        assert extdeg == 3
        K24 = Kf
        power = 24
    # Transform polynomial roots x => x**power => cubic(x**power)
    pol = wpoly.monic()
    if K24.degree() == Kf.degree() and K24 is not Kbase:
        # Adams operator will not give any gain
        # Apply the whole projection
        x = polygen(K24)
        t0 = cputime()
        pol = ((x**24 - 16) ** 3 * (x**24).inverse_mod(pol)).minpoly_mod(pol)
        verbose(
            f"minpoly_mod reduced field degree {Kf.degree()} => {Kbase.degree()}", t=t0
        )
    elif power > 1:
        assert K24 is Kbase and f**24 in Kbase
        # We can reduce the degree in several steps.
        t0 = cputime()
        pol = _fast_adams_operator(pol, power)
        verbose(
            f"adams_operator x^{power} reduced field degree {Kf.degree()} => {Kbase.degree()}",
            t=t0,
        )
    else:
        assert power == 1 and Kf == Kbase
    pol = pol.change_ring(Kbase)
    x = wpoly.parent().gen()
    for ff, mult in _fast_pari_roots(pol):
        if K24 is not Kbase:
            # We applied operator (x^24-16)^3/x^24 on roots
            j2 = ff
        else:
            # We applied operator x^power on roots
            j2 = ff ** (24 // power)
            j2 = (j2 - 16) ** 3 / j2
        wf = wpoly.gcd((x**24 - 16) ** 3 - j2 * x**24)
        assert wf.degree() == 1
        f2 = wf.roots()[0][0]
        yield f2, j2, mult


def _fast_adams_operator(p, k):
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


def _fast_pari_roots(poly):
    if not poly.is_squarefree():
        return poly.roots()
    # it's squarefree
    paripoly = poly._pari_with_name()
    R = poly.base_ring()
    return [(R(r), 1) for r in paripoly.polrootsmod()]


def _fast_elkies(E1, E2, l):
    """
    Compute the unique normalized isogeny of degree l between E1 and E2

    This is the fastElkies' algorithm from:

    Bostan, Salvy, Morain, Schost
    Fast algorithms for computing isogenies between elliptic curves
    https://arxiv.org/pdf/cs/0609020.pdf

    >>> from sage.all import GF, EllipticCurve
    >>> E1 = EllipticCurve(GF(167), [153, 112])
    >>> E2 = EllipticCurve(GF(167), [56, 40])
    >>> _fast_elkies(E1, E2, 13)
    x^6 + 139*x^5 + 73*x^4 + 139*x^3 + 120*x^2 + 88*x

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
