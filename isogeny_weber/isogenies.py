"""
Compute isogenies of a given prime degree l using Weber modular
polynomials.
"""

import bisect
import itertools
import math

from sage.all import (
    ZZ,
    RR,
    GF,
    EllipticCurve,
    polygen,
    cputime,
    pari,
    mod,
    Zmod,
    CRT,
    CRT_basis,
    prod,
    factor,
    two_squares,
    BinaryQF,
)

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
    eqf24 = (x - 16) ** 3 - j * x
    if eqf24.is_irreducible():
        # The root of the cubic polynomial in the cubic extension
        # always has a 24-th root.
        if K.degree() == 1:
            Kext = K.extension(modulus=eqf24, names="f24")
            f = Kext.gen().nth_root(24)
        else:
            # no extension towers in Sage
            Kext = K.extension(3, names="x")
            f = eqf24.roots(ring=Kext)[0][0].nth_root(24)
    else:
        # There is a root.
        f = None
        for f24 in eqf24.roots(multiplicities=False):
            K_ = (x**24 - f24).splitting_field("a")
            if f is None or K_.degree() < f.parent().degree():
                Kext, f = K_, K_(f24).nth_root(24)
    assert f is not None and eqf24(f**24) == 0
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
            assert (
                ker.degree() == (l - 1) // 2
            ), f"{l=} kernel degree {ker.degree()}\nE1: {E}\nE2: {E2}"
            verbose(f"computed normalized isogeny of degree {l}", t=t0)
            yield E.isogeny(ker, codomain=E2, degree=l, check=check)


def _weber_poly_descent(wpoly, Kbase, f, force=False):
    """
    Compute descent from wpoly to the base field and returns
    transition functions to (f, j) coordinates.

    force: whether descent is mandatory, e.g. for SEA
    """
    # Use built-in root solving if already working on the base field
    # or if extension field is small.
    if f in Kbase or (not force and f.parent().order().bit_length() < 256):

        def convert(r):
            r = f.parent()(r)
            yield r, (r**24 - 16) ** 3 / r**24

        return wpoly, convert

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
        # Apply the whole projection: beware that complexity is
        # not linear in l.
        x = polygen(K24)
        t0 = cputime()
        pol = ((x**24 - 16) ** 3 * (x**24).inverse_mod(pol)).minpoly_mod(pol)
        verbose(
            f"minpoly_mod reduced field degree {Kf.degree()} => {Kbase.degree()}",
            t=t0,
            level=2,
        )
    elif power > 1:
        assert K24 is Kbase and f**24 in Kbase
        # We can reduce the degree in several steps.
        t0 = cputime()
        pol = _fast_adams_operator(pol, power)
        verbose(
            f"adams_operator x^{power} reduced field degree {Kf.degree()} => {Kbase.degree()}",
            t=t0,
            level=2,
        )
    else:
        assert power == 1 and Kf == Kbase
    pol = pol.change_ring(Kbase)
    x = wpoly.parent().gen()
    if K24 is not Kbase:
        # We applied operator (x^24-16)^3/x^24 on roots
        def convert(r):
            r = Kbase(r)
            wf = wpoly.gcd((x**24 - 16) ** 3 - r * x**24)
            # It may have multiple roots, corresponding
            # to resolutions of double points of the j-modular curve.
            # The derivatives will be valid!
            # FIXME: Can it have more than 2 roots?
            assert wf.degree() <= 2, wf
            for f2 in wf.roots(multiplicities=False):
                yield f2, r

    else:
        # We applied operator x^power on roots
        def convert(r):
            r = Kbase(r)
            j2 = r ** (24 // power)
            j2 = (j2 - 16) ** 3 / j2
            wf = wpoly.gcd(x**power - r)
            # It may have multiple roots, corresponding
            # to resolutions of double points of the j-modular curve.
            # The derivatives will be valid!
            assert wf.degree() <= 2, wf
            for f2 in wf.roots(multiplicities=False):
                yield f2, j2

    return pol, convert


def _weber_poly_roots(wpoly, Kbase, f, j):
    """
    Compute roots of the Weber modular polynomial Wl(f, x)
    and iterates over (f2, j2, multiplicity)
    """
    pol, map_ = _weber_poly_descent(wpoly, Kbase, f)
    for r, mult in _fast_pari_roots(pol):
        for f2, j2 in map_(r):
            yield f2, j2, mult


def _weber_poly_roots_factors(wpoly, Kbase, f):
    """
    Compute roots of the Weber modular polynomial Wl(f, x)
    assumed squarefree, but also the degree of remaining factors.
    """
    pol, map_ = _weber_poly_descent(wpoly, Kbase, f, force=True)
    # We require analysis over the base field
    assert pol.base_ring().order() == Kbase.order()
    by_degree = pol._pari_with_name().factormodDDF()
    roots = []
    r = None
    for i in range(by_degree.nrows()):
        fac = by_degree[i, 0]
        deg = by_degree[i, 1]
        if deg == 1:
            roots = fac.polrootsmod()
        else:
            if r is not None:
                ValueError("conflicting modular polynomial factor size {r} vs {deg}")
            r = deg
    return [(f, j) for rt in roots for f, j in map_(rt)], r


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


# Point counting
#
# Bibliography:
# François Morain, Calcul du nombre de points sur une courbe elliptique
# dans un corps fini : aspects algorithmiques
# http://www.numdam.org/item/JTNB_1995__7_1_255_0.pdf
#
# René Schoof, Counting points on elliptic curves over finite fields
# http://www.numdam.org/item/JTNB_1995__7_1_219_0.pdf


def trace_of_frobenius(E, weber_db=Database()):
    """
    Compute the trace of Frobenius endomorphism for curve E
    defined over a prime field, as an element of Z.

    Only curves over GF(p) where p is prime (not a prime power)
    are supported.
    """
    t_start = cputime()
    K = E.base_ring()
    p = K.characteristic()
    if not K.is_field() or not K.is_finite() or K.degree() > 1:
        raise ValueError(f"Base ring {K} is not a prime field")
    j = E.j_invariant()
    verbose(f"j={j}")

    def trace_j0():
        if p % 3 == 2:
            # E is supersingular
            verbose(f"E is supersingular")
            tr = 0
        else:
            # Factor p=Norm(u-jv) in Q(sqrt(-3)) where j=zeta(3)
            u, v = BinaryQF(1, -1, 1).solve_integer(p)
            verbose(
                f"Complex multiplication by Z[j], p=Norm({u}+{v}j), trace=±{2*u-v},±{2*v-u},±{u+v}"
            )
            # j (u+vj) = uj + vj² = -v + (u-v)j
            # j²(u+vj) = v + uj²
            trs = [2 * u - v, v - 2 * u, 2 * v - u, u - 2 * v, u + v, -u - v]
            while len(trs) > 1:
                pt = E.random_point()
                trs = [t for t in trs if ZZ(p + 1 - t) * pt == 0]
                verbose(f"{len(trs)} candidate traces after checking a random point")
            tr = trs[0]
        verbose(f"Trace of Frobenius: {tr}", t=t_start)
        E.set_order(p + 1 - tr, check=True, num_checks=8)
        verbose(f"Order of E checked using 8 random points")
        return tr

    def trace_j1728():
        if p % 4 == 3:
            # E is supersingular
            verbose(f"E is supersingular")
            tr = 0
        else:
            u, v = two_squares(p)
            verbose(
                f"Complex multiplication by Z[i], p=Norm({u}+{v}i), trace=±{2*u},±{2*v}"
            )
            trs = [2 * u, -2 * u, 2 * v, -2 * v]
            while len(trs) > 1:
                pt = E.random_point()
                trs = [t for t in trs if ZZ(p + 1 - t) * pt == 0]
                verbose(f"{len(trs)} candidate traces after checking a random point")
            tr = trs[0]
        verbose(f"Trace of Frobenius: {tr}", t=t_start)
        E.set_order(p + 1 - tr, check=True, num_checks=8)
        verbose(f"Order of E checked using 8 random points")
        return tr

    if j == K(0):
        return trace_j0()
    if j == K(1728):
        return trace_j1728()

    A, B = E.a4(), E.a6()
    x = polygen(K)
    # Compute shared data: f-invariant and extension field pattern.
    eqf24 = (x - 16) ** 3 - j * x
    if eqf24.is_irreducible():
        # The root of the cubic polynomial in the cubic extension
        # always has a 24-th root.
        Kext = K.extension(modulus=eqf24, names="f24")
        f = Kext.gen().nth_root(24)
    else:
        # There is a root.
        f = None
        for f24 in eqf24.roots(multiplicities=False):
            deg = lambda _f: _f.degree()
            fac = min((_f for _f, _ in (x**24 - f24).factor()), key=deg)
            Kext = K.extension(modulus=fac, names="f")
            f = Kext.gen()
    assert f is not None and eqf24(f**24) == 0

    verbose(f"f-invariant in field GF(p^{Kext.degree()})")

    # How much bruteforce can we do?
    atkin_budget = int(p.bit_length() ** 4)

    crt_mods = []
    crt_vals = []

    atkin_choices = {}
    atkin_gain = 1
    sort_atkins = []
    best_atkins = []

    t2 = 1 + len((x**3 + A * x + B).roots())
    verbose(f"2-torsion has order {factor(t2)}")
    if t2 == 4:
        # Order divisible by 4.
        crt_mods.append(ZZ(4))
        crt_vals.append((p + 1) % 4)
    else:
        crt_mods.append(ZZ(2))
        crt_vals.append(t2)

    target = 4 * (K.order().isqrt() + 1)
    ls = sorted(weber_db.keys())
    if prod(ls) < target:
        raise ValueError(f"not enough modular polynomials for {p.bit_length()}-bit p")

    scalar_muls = {}
    for l in ls:
        wp = weber_db.modular_polynomial(l, base_ring=Kext, y=f)
        t0 = cputime()
        roots, r = _weber_poly_roots_factors(wp, K, f)
        if any(j == K(1728) for _, j in roots):
            verbose(f"Curve is {l}-isogenous to j=1728")
            return trace_j1728()
        if any(j == K(0) for _, j in roots):
            verbose(f"Curve is {l}-isogenous to j=0")
            return trace_j0()
        if len(roots) == 2:
            verbose(f"Elkies prime {l}", t=t0)
            tr = elkies_trace(E, l, f, r, wp, roots, weber_db, scalar_muls=scalar_muls)
            crt_mods.append(l)
            crt_vals.append(ZZ(tr))
        elif len(roots) == 0:
            verbose(f"Atkin prime {l}", t=t0)
            ts = atkin_traces(p, l, r)
            if len(ts) == 1:
                verbose(f"factor degree {r} => trace={list(ts)[0]}")
                crt_mods.append(l)
                crt_vals.append(ts.pop())
            else:
                verbose(f"factor degree {r} => {len(ts)} traces")
                atkin_choices[l] = ts
        elif len(roots) in (1, l + 1):
            if len(roots) == l + 1:
                verbose(f"Volcano inner node: t^2 - 4p is divisible by {l}^2", t=t0)
            else:
                verbose(f"Double root: t^2 - 4p is divisible by {l}", t=t0)
                r = 1
            tr = elkies_trace(E, l, f, r, wp, roots, weber_db, scalar_muls)
            crt_mods.append(l)
            crt_vals.append(ZZ(tr))
        if prod(crt_mods) * atkin_gain > target:
            break
        # Recompute best atkins
        sort_atkins = sorted(
            atkin_choices,
            key=lambda t: -math.log(t) / math.log(len(atkin_choices[t])),
        )
        atkin_cost = 1
        best_atkins = sort_atkins
        for i, _l in enumerate(sort_atkins):
            atkin_cost *= len(atkin_choices[_l])
            if atkin_cost > atkin_budget:
                best_atkins = sort_atkins[:i]
                break
        atkin_cost = prod(len(atkin_choices[_l]) for _l in best_atkins)
        atkin_gain = prod(best_atkins) // atkin_cost // 2 + 1
        if crt_mods[-1] == l and len(crt_mods) % 5 == 0:
            verbose(f"Progress: {prod(crt_mods).bit_length()} known bits", t=t_start)
            verbose(
                f"Progress: {atkin_gain.bit_length()} theoretical bits from Atkin primes {best_atkins} (2^{atkin_cost.bit_length()} brute force)"
            )
            candidates = target // atkin_gain // prod(crt_mods) + 1
            if candidates >> 100:
                candidates = RR(candidates)
            verbose(f"~{candidates} remaining candidates")
    prod_e = prod(crt_mods)
    verbose(f"Product of Elkies primes {prod_e} ({prod_e.bit_length()} bits)")
    verbose(
        f"Additional Atkin prime information {atkin_gain} ({atkin_gain.bit_length()} bits)"
    )
    verbose(f"Traces: {list(zip(crt_mods, crt_vals))}", level=2)
    # Apply Atkin algorithm and CRT
    tr = CRT(crt_vals, crt_mods)
    if tr > prod(crt_mods) // 2:
        tr -= prod(crt_mods)
    sort_atkins = sorted(
        atkin_choices,
        key=lambda t: -math.log(t) / math.log(len(atkin_choices[t])),
    )
    candidates = target // atkin_gain // prod(crt_mods) + 1
    while candidates > ZZ(atkin_budget).isqrt() and len(best_atkins) < len(sort_atkins):
        best_atkins = sort_atkins[: len(best_atkins) + 1]
        atkin_cost = prod(len(atkin_choices[_l]) for _l in best_atkins)
        atkin_gain = prod(best_atkins) // atkin_cost + 1
        candidates = target // atkin_gain // prod(crt_mods) + 1
        verbose(
            f"Select additional Atkin prime {best_atkins[-1]}, ~{candidates} candidates"
        )
    for al in best_atkins:
        verbose(f"Atkin prime {al}: traces {sorted(atkin_choices[al])}")
    if best_atkins:
        trs = match_atkin(2 * p.isqrt() + 1, prod_e, tr, best_atkins, atkin_choices)
        while len(trs) > 1:
            # Extremely rare
            pt = E.random_point()
            trs = [t for t in trs if ZZ(p + 1 - t) * pt == 0]
            verbose(f"{len(trs)} candidate traces after checking a random point")
        tr = trs[0]
    assert abs(tr) <= 2 * p.isqrt(), tr
    verbose(f"Trace of Frobenius: {tr}", t=t_start)
    checks = len(crt_mods)
    E.set_order(p + 1 - tr, check=True, num_checks=checks)
    verbose(f"Order of E checked using {checks} random points")
    return tr


def atkin_traces(p, l, r):
    """
    Returns the list of possible Frobenius traces from the known
    order of Frobenius in GF(l^2)/GF(l)
    """
    # If kernels are defined over GF(p^r), Frobenius^r has
    # rational eigenvalues
    # In particular: t^2 = (z + z^-1)^2 p where z is a r-th root of unity.
    # (Schoof, Proposition 6.2)
    Kl2 = GF(l**2)
    x = polygen(Kl2)
    traces = set()
    for t in range(l):
        ab = (x**2 - t * x + p).roots(ring=Kl2, multiplicities=False)
        if len(ab) == 2:
            a, b = ab
            if (a / b).multiplicative_order() == r:
                traces.add(t)
    return sorted(traces)


def match_atkin(bound, crtmod, crtval, atk_primes, atk_traces: dict):
    t0 = cputime()
    assert all(ZZ(l).is_prime() for l in atk_primes)
    assert all(crtmod % l != 0 for l in atk_primes)
    # Separate atkin primes in 2 sets with similar product size
    cost = prod(len(atk_traces[_l]) for _l in atk_primes)
    cost1 = 1
    atk1 = []
    for l in sorted(atk_primes):
        mid = cost1 * ZZ(len(atk_traces[l])).isqrt()
        if mid * mid > cost or len(atk1) + 1 == len(atk_primes):
            break
        cost1 *= len(atk_traces[l])
        atk1.append(l)
    atk2 = [l for l in atk_primes if l not in atk1]
    verbose(f"set A = {cost1} traces modulo {'*'.join(str(a) for a in atk1)}")
    verbose(f"set B = {cost//cost1} traces modulo {'*'.join(str(a) for a in atk2)}")

    # Apply CRT to each set
    b1 = CRT_basis(atk1)
    p1 = prod(atk1)
    crt1 = []
    for tup in itertools.product(*[atk_traces[_l] for _l in atk1]):
        crt1.append(sum(ti * bi1 for ti, bi1 in zip(tup, b1)) % p1)
    assert all(c % l in atk_traces[l] for c in crt1 for l in atk1)

    b2 = CRT_basis(atk2)
    p2 = prod(atk2)
    crt2 = []
    for tup in itertools.product(*[atk_traces[_l] for _l in atk2]):
        crt2.append(sum(ti * bi2 for ti, bi2 in zip(tup, b2)) % p2)
    assert all(c % l in atk_traces[l] for c in crt2 for l in atk2)

    # Combine with known value
    a0, a1 = CRT_basis([crtmod, p1])
    crt1 = [(a0 * crtval + a1 * c) % (crtmod * p1) for c in crt1]

    verbose(f"Trace bound is {bound}", level=2)

    # Combine again, make elements centered
    mod = crtmod * p1 * p2
    verbose(f"Total CRT modulus {mod}", level=2)
    pa, pb = CRT_basis([crtmod * p1, p2])
    crt1 = [(pa * c + mod // 2) % mod - mod // 2 for c in crt1]
    crt2 = [(pb * c + mod // 2) % mod - mod // 2 for c in crt2]
    crt2 += [c - mod for c in crt2] + [c + mod for c in crt2]
    crt2.sort()
    assert mod > 4 * bound

    # Now find a match
    matches = []
    for c1 in crt1:
        c2min, c2max = -bound - c1, bound - c1
        imin = bisect.bisect_left(crt2, c2min)
        imax = bisect.bisect_right(crt2, c2max)
        for i in range(imin, imax):
            if abs(c1 + crt2[i]) < bound:
                matches.append(c1 + crt2[i])
    verbose(f"{len(matches)} candidates found after CRT meet-in-the-middle", level=2)
    res = []
    for m in matches:
        if all(m % l in ts for l, ts in atk_traces.items()):
            res.append(m)
            # verbose(f"possible trace {m}", level=3)
    verbose(f"Atkin match done: {len(res)} solutions", t=t0)
    return res


def elkies_trace(E, l, f, r, wp, roots, weber_db, scalar_muls: dict):
    """
    Compute Frobenius trace on isogeny kernel

    l: degree of isogeny
    f: f-invariant of E
    r: order of Frobenius
    wp: Weber modular polynomial specialized for f
    roots: roots of wp(f,x)
    weber_db: database of modular polynomials
    """
    if r == 2:
        # Frobenius acts by conjugation
        # Eigenvalues are ±sqrt(p)
        verbose(f"Trivial trace 0", level=1)
        return 0

    A, B, j = E.a4(), E.a6(), E.j_invariant()
    K, Kext = E.base_ring(), f.parent()

    # Only one eigenvalue is needed
    f2, j2 = roots[0]
    wx = weber_db.modular_polynomial(l, base_ring=Kext, y=f2)
    phix = wx.derivative()(f) * (3 * (f2**24 - 16) ** 2 - j2) / f2
    phiy = wp.derivative()(f2) * (3 * (f**24 - 16) ** 2 - j) / f
    jj = 18 * B / A * j
    jj2 = K(-phix * jj / (l * phiy))
    mm = jj2 / j2
    kk = jj2 / (1728 - j2)
    E2 = EllipticCurve(K, [l**4 * mm * kk / 48, l**6 * mm**2 * kk / 864])
    assert E2.j_invariant() == j2
    t0 = cputime()
    ker = _fast_elkies(E, E2, l)
    verbose(f"computed isogeny kernel of degree {l}", t=t0, level=2)

    # On the given eigenspace:
    # Frob(x) = k x for k a primitive r-th root modulo l
    # Frob^2 - t Frob + p = 0
    # Also we know that k^2 = z p where z is a primitive r-th root of unity.

    Kx, x = ker.parent().objgen()
    p = K.characteristic()
    # Use PARI to get Frobenius
    frob_pari = pari.Mod(x._pari_with_name(), ker._pari_with_name()) ** p
    frob = Kx(frob_pari.lift())
    verbose(f"computed frobenius on kernel", t=t0, level=2)

    # Confirm sign using y.
    # Y ^ (p-1) = (X^3 + A X + B)^(p-1)/2
    y_pm1_pari = pari.Mod(
        (x**3 + A * x + B)._pari_with_name(), ker._pari_with_name()
    ) ** ((p - 1) // 2)
    y_pm1 = Kx(y_pm1_pari.lift())
    # Frob(X,Y) = (X^p, Y^(p-1) Y)

    if frob == x:
        # Eigenvalue is ±1, the other one is ±p
        # Y^p is either Y or -Y
        eigen = 1 if y_pm1[0] == 1 else -1
        assert y_pm1 == Kx(eigen)
        verbose(f"skipped discrete log, eigenvalue is {eigen}", t=t0, level=1)
        return eigen * (1 + mod(p, l))

    # Too lazy to implement point addition.
    # Instead we compute a discrete log in Aut(Z/lZ) = (Z/lZ)*
    # Solve eigenvalue, this is a discrete log in (Z/lZ)x
    # It will cost O(sqrt(l)) modular compositions of degree l
    # Look for g^ak = Frob g^b
    g = int(Zmod(l).multiplicative_generator())
    # g is hopefully very small, g <= 11 for l < 1000 except in 7 cases
    if g not in scalar_muls:
        scalar_muls[g] = E.multiplication_by_m(g)
    # Beware they are multivariates.
    gx, gy = scalar_muls[g]
    gx = Kx(gx.numerator()) * Kx(gx.denominator()).inverse_mod(ker)
    gx %= ker
    gy = Kx(gy.numerator().coefficient([None, 1])) * Kx(gy.denominator()).inverse_mod(
        ker
    )
    gy %= ker
    autg = _modular_automorphism(ker, gx)

    if r == 1:
        # Eigenvalue is a square root of p, no need to do a group discrete log.
        eigen = mod(p, l).sqrt()
        verbose(f"skipped discrete log, eigenvalue is ±{eigen}", t=t0, level=2)
    else:
        bs = [x, gx]
        step = ZZ(l).isqrt() + 1
        while len(bs) < step:
            bs.append(autg(bs[-1]))
        autg_giant = _modular_automorphism(ker, autg(bs[-1]))

        frobi = frob
        i = 0
        while frobi not in bs and i < l:
            frobi = autg_giant(frobi)
            i += 1
        j = bs.index(frobi)

        # Now Frobenius * g**(step*i) == ±g**j
        eigen = pow(g, j - step * i, l)
        verbose(f"solved discrete log, eigenvalue is ±{eigen}", t=t0, level=2)

    eigen = mod(eigen, l)
    dlog = eigen.log(g)
    dlog2 = (-eigen).log(g)
    if dlog >= dlog2:
        eigen, dlog = -eigen, dlog2

    # (x[k],y[k]) = g^k (x,y) = (autg(x[k-1]), gy(x[k-1]) * y[k-1])
    # so y[k] / y[k-1] = gy(x[k-1])
    # y[k] = gy(x[k-1]) * gy(x[k-2]) * ... * gy(x)
    #      = gy * autg(gy) * ... * autg^(k-1)(gy)
    yk = gy
    ggy = gy
    for _ in range(dlog - 1):
        ggy = autg(ggy)
        yk = (yk * ggy) % ker
    if yk != y_pm1:
        assert yk == -y_pm1
        eigen = -eigen
    tr = eigen + mod(p, l) / eigen
    verbose(f"Elkies {l} found eigenvalue {eigen} trace={tr}", t=t0, level=1)
    return tr


def _modular_automorphism(modulus, xp):
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
