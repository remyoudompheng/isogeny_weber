"""
Compute isogenies of a given prime degree l using Weber modular
polynomials.
"""

import bisect
import itertools
import math
import time

from sage.all import (
    BinaryQF,
    CRT,
    CRT_basis,
    EllipticCurve,
    GF,
    ZZ,
    cputime,
    euler_phi,
    primes,
    factor,
    legendre_symbol,
    mod,
    polygen,
    prod,
    two_squares,
    parallel,
)

from sage.misc.verbose import verbose

from .poldb import Database
from .poldb_compute import compute_modular_polynomial, weber_modular_poly_coeffs
from .polynomials import (
    frobenius_mod,
    fast_adams_operator,
    powmod,
    modular_composition,
    xp_from_cubicp,
    mul_trunc,
    inv_trunc,
)

_builtin_database = Database()

def isogenies_prime_degree_weber(E, l, weber_db=None, only_j=False, check=True):
    """
    Returns an iterator over outgoing isogenies of degree l
    with domain E.

    l must be a prime level in the Weber modular polynomial
    database (usually l < 1000).

    check: run the expensive check in isogeny constructor (default=True)
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
    if weber_db is None:
        weber_db = _builtin_database

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
                if f in K:
                    Kext, f = K, K(f)
    assert f is not None and eqf24(f**24) == 0
    verbose(f"domain j={j}")
    verbose(f"f-invariant in field {Kext}")
    t0 = cputime()
    if l in weber_db:
        wxy = None
        wp = weber_db.modular_polynomial(l, base_ring=Kext, y=f)
    else:
        wxy = weber_modular_poly_coeffs(l)
        wp = compute_modular_polynomial(l, base_ring=Kext, y=f, coeffs=wxy)
        verbose(f"Computed modular polynomial of level {l}", t=t0)
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
            if wxy is not None:
                wx = compute_modular_polynomial(l, base_ring=Kext, y=f2, coeffs=wxy)
            else:
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
    if f.parent() is Kbase or (not force and f.parent().order().bit_length() < 256):

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
        pol = fast_adams_operator(pol, power)
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
    pol, map_ = _weber_poly_descent(wpoly, Kbase, f, force=True)
    if not pol.is_squarefree():
        roots = pol.roots()
    else:
        # Compute Frobenius using a fast library.
        assert pol.base_ring().order() == Kbase.order()
        p = Kbase.order()
        frob = frobenius_mod(pol, p)
        (x,) = pol.variables()
        roots = (frob - x).gcd(pol).roots()
    for r, mult in roots:
        for f2, j2 in map_(r):
            yield f2, j2, mult


def _weber_poly_roots_frobenius(wpoly, Kbase, f):
    """
    Compute roots of the Weber modular polynomial Wl(f, x)
    assumed squarefree, and the Frobenius endomorphism
    modulo the base field polynomial obtained by descent.
    """
    pol, map_ = _weber_poly_descent(wpoly, Kbase, f, force=True)
    # We require analysis over the base field
    assert pol.base_ring().order() == Kbase.order()
    # We don't compute a full distinct-degree decomposition.
    # Instead, compute the Frobenius polynomial and use it
    # to find small degree factors.
    p = Kbase.order()
    frob = frobenius_mod(pol, p)
    (x,) = pol.variables()
    roots = (frob - x).gcd(pol).roots(multiplicities=False)
    return [(f, j) for rt in roots for f, j in map_(rt)], pol, frob


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
    C = inv_trunc(1 + A * x**4 + B * x**6, 4 * l)
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
    # Compute U = 1/T^2
    # Reconstruct N(1/x) / D(1/x) = U
    T = Rx([S[2 * i + 1] for i in range(2 * l)])
    U = inv_trunc(mul_trunc(T, T, 2 * l), 2 * l)
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
#
# Pierrick Gaudry, François Morain.
# Fast algorithms for computing the eigenvalue in the Schoof-Elkies-Atkin algorithm.
# ISSAC '06: Proceedings of the 2006 international symposium on symbolic and algebraic computation
# Jul 2006, Genoa, Italy, pp.109 - 115, ⟨10.1145/1145768.1145791⟩. ⟨inria-00001009⟩
# https://hal.science/inria-00001009


def trace_of_frobenius(E, weber_db=_builtin_database, threads=1):
    """
    Compute the trace of Frobenius endomorphism for curve E
    defined over a prime field, as an element of Z.

    Only curves over GF(p) where p is prime (not a prime power)
    are supported.
    """
    t_start = time.time()
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
        verbose(f"Trace of Frobenius: {tr} elapsed={time.time()-t_start}s")
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
        verbose(f"Trace of Frobenius: {tr} elapsed={time.time()-t_start}s")
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
    # The real cost will be about sqrt(budget), preferably less than 10^6
    atkin_budget = int(100 * p.bit_length() ** 3)

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
    ls = list(primes(5, p.bit_length()))
    assert prod(ls).isqrt() >= target

    args = [(E, l, f, K, Kext, weber_db) for l in ls]
    for lidx, (_, (l, traces, j2s)) in enumerate(
        possibly_parallel(threads)(trace_of_frobenius_modl)(args)
    ):
        if K(1728) in j2s:
            verbose(f"Curve is {l}-isogenous to j=1728")
            return trace_j1728()
        if K(0) in j2s:
            verbose(f"Curve is {l}-isogenous to j=0")
            return trace_j0()
        if len(traces) == 1:
            crt_mods.append(l)
            crt_vals.append(ZZ(list(traces)[0]))
        else:
            atkin_choices[l] = sorted(traces)
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
        candidates, atkin_gain = _sea_progress(
            target,
            crt_mods,
            atkin_choices,
            best_atkins,
            log_ts=t_start if (lidx % 5 == 4) else None,
        )
        # Exit if done
        if candidates < p.bit_length():
            break
    verbose(f"~{candidates} remaining candidates")
    prod_e = prod(crt_mods)
    verbose(f"Product of Elkies primes {prod_e} ({prod_e.bit_length()} bits)")
    verbose(
        f"Additional Atkin prime information {atkin_gain} ({atkin_gain.bit_length()} bits)"
    )
    verbose(f"Traces: {list(zip(crt_mods, crt_vals))}", level=2)
    # Apply Atkin algorithm and CRT
    tr = CRT(crt_vals, crt_mods)
    crt_prod = prod(crt_mods)
    if tr > crt_prod // 2:
        tr -= crt_prod
    verbose(f"CRT result: {tr}", t=t_start)
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
        verbose(f"Atkin prime {al}: traces {sorted(atkin_choices[al])}", level=2)
    if best_atkins:
        trs = match_atkin(2 * p.isqrt() + 1, prod_e, tr, best_atkins, atkin_choices)
    else:
        bound = 2 * p.isqrt() + 1
        trs = list(range(tr, bound + 1, crt_prod))
        trs += list(range(tr - crt_prod, -bound - 1, -crt_prod))
        verbose(f"{len(trs)} candidate traces after CRT")
    while len(trs) > 1:
        pt = E.random_point()
        trs = [t for t in trs if ZZ(p + 1 - t) * pt == 0]
        verbose(f"{len(trs)} candidate traces after checking a random point")
    tr = trs[0]
    assert abs(tr) <= 2 * p.isqrt(), tr
    verbose(f"Trace of Frobenius: {tr} elapsed={time.time()-t_start}s")
    checks = len(crt_mods)
    E.set_order(p + 1 - tr, check=True, num_checks=checks)
    verbose(f"Order of E checked using {checks} random points")
    return tr


def trace_of_frobenius_modl(E, l, f, K, Kext, weber_db):
    t0 = cputime()
    if l in weber_db:
        wxy = None
        wp = weber_db.modular_polynomial(l, base_ring=Kext, y=f)
    else:
        wxy = weber_modular_poly_coeffs(l)
        wp = compute_modular_polynomial(l, base_ring=Kext, y=f, coeffs=wxy)
        verbose(f"Computed modular polynomial of level {l}", t=t0, level=2)
    roots, wdescent, wfrob = _weber_poly_roots_frobenius(wp, K, f)
    p = K.characteristic()
    verbose(f"{len(roots)} roots for modular equation at level {l}", t=t0, level=2)
    j2s = [j for _, j in roots]
    if K(0) in j2s or K(1728) in j2s:
        return l, None, j2s
    if len(roots) == 2:
        r = None
        tr = elkies_trace(E, l, f, wp, roots, weber_db, wxy=wxy)
        verbose(f"processed Elkies prime {l} (trace={tr})", t=t0)
        return l, [tr], j2s
    elif len(roots) == 0:
        # Compute order of Frobenius
        # We are only interested in values of r giving few traces
        # at most 32 and at most 2 sqrt(l)
        # Parity of (l+1)/r is related to (p|l) (Schoof, Proposition 6.3)
        parity_s = 0 if legendre_symbol(p, l) == 1 else 1
        rs = [d for d in ZZ(l + 1).divisors() if ((l + 1) // d) % 2 == parity_s]
        good_rs = [_r for _r in rs if euler_phi(_r) <= min(32, 2 * ZZ(l).isqrt())]
        if good_rs:
            r = _order_of_frobenius(wdescent, wfrob, limit=max(good_rs))
            if r is not None:
                rs = [r]
        ts = atkin_traces(p, l, rs)
        if len(ts) == 1:
            verbose(f"factor degree {r} => trace={list(ts)[0]}", level=2)
            verbose(f"processed Atkin prime {l} (trace={list(ts)[0]})", t=t0)
            return l, ts, j2s
        else:
            r = rs[0] if len(rs) == 1 else "unknown"
            verbose(f"factor degree {r} => {len(ts)} traces", level=2)
            verbose(f"processed Atkin prime {l} ({len(ts)} traces)", t=t0)
            return l, ts, j2s
    elif len(roots) in (1, l + 1):
        if len(roots) == l + 1:
            verbose(
                f"Volcano inner node: t^2 - 4p is divisible by {l}^2", t=t0, level=2
            )
        else:
            verbose(f"Double root: t^2 - 4p is divisible by {l}", t=t0, level=2)
            r = 1
        tr = elkies_trace(E, l, f, wp, roots, weber_db, wxy=wxy)
        verbose(f"processed Elkies prime {l} (trace={tr}, double root)", t=t0)
        return l, [tr], j2s
    else:
        print("IMPOSSIBLE")
        print(l)
        print(roots)
        return l, list(range(l)), j2s


def possibly_parallel(num_cores):
    if num_cores == 1:

        def _wrap(fun):
            def _fun(args):
                for a in args:
                    yield ((a,), None), fun(*a)

            return _fun

        return _wrap
    return parallel(num_cores)


def _sea_progress(target, crt_mods, atkin_choices, best_atkins, log_ts=None):
    atkin_cost = prod(len(atkin_choices[_l]) for _l in best_atkins)
    atkin_gain = prod(best_atkins) // atkin_cost + 1
    atkin_gain2 = (
        prod(atkin_choices) // prod(len(_trs) for _trs in atkin_choices.values()) + 1
    )
    nE = target // prod(crt_mods) + 1
    nEA = target // prod(crt_mods) // atkin_gain + 1
    nEAA = target // prod(crt_mods) // atkin_gain2 + 1

    def fmt(n):
        return f"~2^{n.bit_length()-1}" if n >> 40 else f"~{n}"

    if log_ts:
        verbose(
            f"Progress: {prod(crt_mods).bit_length()} known bits + {atkin_gain.bit_length()} from {len(best_atkins)} Atkin primes (elapsed={time.time()-log_ts}s)"
        )
        verbose(
            f"Selected Atkin primes: {best_atkins} (~2^{atkin_cost.bit_length()} traces)",
            level=2,
        )
        verbose(
            f"Remaining candidates: {fmt(nE)} (Elkies), {fmt(nEA)} (Elkies + {len(best_atkins)} Atkin), {fmt(nEAA)} (all info)"
        )
    return nEA, atkin_gain


def _order_of_frobenius(modulus, frob, limit=None):
    """
    Compute order of Frobenius endomorphism for a polynomial
    having factors of equal degree (very common in isogenies).
    """
    if limit is None:
        limit = modulus.degree()
    x = modulus.parent().gen()
    if frob == x:
        return 1

    def comp(f, g):
        return modular_composition(f, g, modulus)

    t0 = cputime()
    ops = 0
    if limit <= 5:
        fn, exp = frob, 1
        while fn != x:
            fn, exp = comp(frob, fn), exp + 1
            ops += 1
            if exp >= limit:
                break
        if fn == x:
            verbose(
                f"Found Frobenius order={exp} using {ops} mod compositions",
                t=t0,
                level=2,
            )
            return exp
    else:
        # BSGS method
        t = ZZ(limit.isqrt() + 1)
        bs = [x, frob]
        while len(bs) < t:
            bs.append(comp(frob, bs[-1]))
            ops += 1
            if bs[-1] == x:
                verbose(
                    f"Found Frobenius order={len(bs)-1} using {ops} mod compositions",
                    t=t0,
                    level=2,
                )
                return len(bs) - 1
        # frobt = Frob^(t*exp)
        frobkt, exp = comp(frob, bs[-1]), 1
        ft = frobkt
        ops += 1
        for _ in range(limit // t):
            if frobkt in bs:
                j = bs.index(frobkt)
                verbose(
                    f"Found Frobenius order={t*exp-j} using {ops} mod compositions",
                    t=t0,
                    level=2,
                )
                return t * exp - j
            frobkt, exp = comp(ft, frobkt), exp + 1
            ops += 1
        if frobkt in bs:
            j = bs.index(frobkt)
            verbose(
                f"Found Frobenius order={t*exp-j} using {ops} mod compositions",
                t=t0,
                level=2,
            )
            return t * exp - j
    verbose(
        f"Frobenius order not found ({limit=}), used {ops} mod compositions",
        t=t0,
        level=2,
    )
    return None


def atkin_traces(p, l, rs: list):
    """
    Returns the list of possible Frobenius traces from the known
    order (or candidate orders) of Frobenius in GF(l^2)/GF(l)
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
            if (a / b).multiplicative_order() in rs:
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
    verbose(f"set A = {cost1} traces modulo {'*'.join(str(a) for a in atk1)}", level=2)
    verbose(
        f"set B = {cost//cost1} traces modulo {'*'.join(str(a) for a in atk2)}", level=2
    )

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
    crt1.sort()
    crt2b = []
    for c in crt2:
        cc = (pb * c + mod // 2) % mod - mod // 2
        for ccc in range(cc, 2 * bound + 1 - crt1[0], mod):
            crt2b.append(ccc)
        for ccc in range(cc, -2 * bound - 1 - crt1[-1], -mod):
            crt2b.append(ccc)
    crt2 = sorted(set(crt2b))
    del crt2b

    # Now find a match
    crt_matches = 0
    matches = []
    for c1 in crt1:
        c2min, c2max = -bound - c1, bound - c1
        imin = bisect.bisect_left(crt2, c2min)
        imax = bisect.bisect_right(crt2, c2max)
        for i in range(imin, imax):
            if abs(m := c1 + crt2[i]) < bound:
                crt_matches += 1
                if all(m % l in ts for l, ts in atk_traces.items()):
                    matches.append(m)
    verbose(f"{crt_matches} candidates found by CRT within Hasse-Weil bound")
    verbose(f"Atkin match done: {len(matches)} solutions", t=t0)
    return matches


def elkies_trace(E, l, f, wp, roots, weber_db, wxy=None):
    """
    Compute Frobenius trace on isogeny kernel

    l: degree of isogeny
    f: f-invariant of E
    wp: Weber modular polynomial specialized for f
    roots: roots of wp(f,x)
    weber_db: database of modular polynomials
    """
    A, B, j = E.a4(), E.a6(), E.j_invariant()
    K, Kext = E.base_ring(), f.parent()

    # Only one eigenvalue is needed
    f2, j2 = roots[0]
    if wxy is not None:
        wx = compute_modular_polynomial(l, base_ring=Kext, y=f2, coeffs=wxy)
    else:
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

    # Don't compute Frobenius using x^p mod h.
    # First compute y^p mod h, then compute x^p from y^2p
    # (See Gaudry-Morain)

    # Y^(p-1) = (X^3 + A X + B)^(p-1)/2
    y_pm1 = powmod(x**3 + A * x + B, (p - 1) // 2, ker)
    # Frob(X,Y) = (X^p, Y^(p-1) Y)

    # But NTL x^p is very fast and handmade modular composition
    # is only interesting when l is "relatively" small,
    # because O(l sqrt(l)) is not far from O(log p).
    if l < p.bit_length() // 3:
        y2p = (y_pm1**2 * (x**3 + A * x + B)) % ker
        frob = xp_from_cubicp(ker, y2p, A, B)
    else:
        frob = frobenius_mod(ker, p)

    verbose(f"computed frobenius on kernel", t=t0, level=2)

    if frob == x:
        # Eigenvalue is ±1, the other one is ±p
        # Y^p is either Y or -Y
        eigen = 1 if y_pm1[0] == 1 else -1
        assert y_pm1 == Kx(eigen)
        verbose(f"skipped discrete log, eigenvalue is {eigen}", t=t0, level=2)
        return eigen * (1 + mod(p, l))

    # There must exist small integers P and Q (less than sqrt(l))
    # such that: P*(x,y) = ±Q*Frob(x,y)
    bound = ZZ(l).isqrt() + 1
    Mul1 = EllMultiples(ker, bound, A, B, x)
    MulF = EllMultiples(ker, bound, A, B, frob)
    x1s = [Mul1.x(i) for i in range(1, bound + 1)]
    eigen = None
    for i in range(1, bound + 1):
        xFi = MulF.x(i)
        if xFi in x1s:
            # i * Frob(x) = j * x
            j = x1s.index(xFi) + 1
            eigen = mod(j, l) / mod(i, l)
            yFi = MulF.y(i, y_pm1)
            y1j = Mul1.y(j, 1)
            if yFi == -y1j:
                eigen = -eigen
            else:
                assert yFi == y1j
            tr = eigen + mod(p, l) / eigen
            verbose(f"Elkies {l} found eigenvalue {eigen} trace={tr}", t=t0, level=2)
            return tr
    raise ValueError("impossible")


class EllMultiples:
    """
    Compute multiples of a given base point, using only x-coordinate
    when possible.

    Reference: https://en.wikipedia.org/wiki/Division_polynomials

    This is the same as division_polynomial_0 in K[x]/modulus,
    with extra caching to save some multiplications.

    Computing N multiples requires:
    * 3N multiplications in psi2 and psi_pm
    * 2.5N multiplications in psi
    * M+I (modular quotient) to emit a x coordinate
    """

    def __init__(self, modulus, m, A, B, x):
        self._x0 = x
        R = modulus.parent()
        self._A, self._B = A, B
        self._4y2 = 4 * (x**3 + A * x + B)
        self._4y2inv = self._4y2.inverse_mod(modulus)
        self._dP = 3 * x**2 + A
        self._ring = R
        self._modulus = modulus
        # Tn(x0) where Tn is the n-th division polynomial if n is odd
        # Tn(x0,y)/2y is n is even
        self._psi = [R(0), R(1), R(1)] + [None for _ in range(m)]
        # The square of _psi
        self._psi2 = [None for _ in range(m + 3)]
        # The product psi_pm[i] = psi[i-1] * psi[i+1]
        self._psi_pm = [None for _ in range(m + 3)]
        # We allocate until n+1 because y(n) needs psi(n+2)

    def x(self, n):
        # x - [n-1][n+1]/[n]^2
        return (
            self._x0 - self.psi_pm(n) * self.psi2(n).inverse_mod(self._modulus)
        ) % self._modulus

    def y(self, n, y0):
        # Compute the y-coordinate of nP, given the y-coordinate of P.
        # [2n] / 2[n]^4
        if n == 1:
            return y0
        # return psi(2n)/psi2(n)^2*y
        res = self.psi_pm(n + 1) * self.psi2(n - 1)
        res -= self.psi_pm(n - 1) * self.psi2(n + 1)
        res *= self._4y2inv
        mod = self._modulus
        res = res * pow(self.psi2(n).inverse_mod(mod), 2, mod)
        return (res * y0) % mod

    def psi(self, i):
        if self._psi[i] is None:
            if i == 3:
                res = (
                    3 * self._x0**4
                    + (6 * self._A) * self._x0**2
                    + (12 * self._B) * self._x0
                    - self._A**2
                )
            elif i == 4:
                res = 2 * self._dP * self.psi(3) - self._4y2**2
            elif i % 2 == 1:
                # [2m+1] = [m+2][m]^3 - [m-1][m+1]^3
                m = i // 2
                res = self.psi_pm(m + 1) * self.psi2(m)
                res -= self.psi_pm(m) * self.psi2(m + 1)
            else:
                # [2m]/2y = [m]/4y^2 ([m+2][m-1]^2 - [m-2][m+1]^2)
                m = i // 2
                res = self.psi_pm(m + 1) * self.psi2(m - 1)
                res -= self.psi_pm(m - 1) * self.psi2(m + 1)
                res *= self._4y2inv
            self._psi[i] = res % self._modulus
        return self._psi[i]

    def psi2(self, i):
        if self._psi2[i] is None:
            if i % 2 == 0:
                # Restore the 4y² factor
                self._psi2[i] = (self.psi(i) ** 2 * self._4y2) % self._modulus
            else:
                self._psi2[i] = self.psi(i) ** 2 % self._modulus
        return self._psi2[i]

    def psi_pm(self, i):
        if self._psi_pm[i] is None:
            self._psi_pm[i] = (self.psi(i - 1) * self.psi(i + 1)) % self._modulus
            if i % 2 == 1:
                # i-1 and i+1 are even, restore the 4y² factor
                self._psi_pm[i] = (self._psi_pm[i] * self._4y2) % self._modulus
        return self._psi_pm[i]
