"""
Compute isogenies of a given prime degree l using Weber modular
polynomials.
"""

from sage.all import ZZ, EllipticCurve, polygen, cputime
from sage.schemes.elliptic_curves.ell_curve_isogeny import (
    compute_isogeny_kernel_polynomial,
)
from sage.misc.verbose import verbose

from .poldb import Database


def isogenies_prime_degree_weber(E, l, weber_db=Database(), only_j=False):
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

    A, B = E.a4(), E.a6()
    x = polygen(K)
    eqf = (x**24 - 16) ** 3 - j * x**24
    eqf2 = min((_f for _f, _ in eqf.factor()), key=lambda _f: _f.degree())
    Kext = eqf2.splitting_field("f")
    f = _fast_pari_roots(eqf2.change_ring(Kext))[0][0]
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
            if mult > 1:
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
            ker = compute_isogeny_kernel_polynomial(E, E2, l)
            verbose(f"computed normalized isogeny of degree {l}", t=t0)
            yield E.isogeny(ker, codomain=E2, degree=l)


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
        # f24 is either in a quadratic or cubic extension of Kbase
        extdeg = Kf.degree() // Kbase.degree()
        if extdeg % 2 == 0 and f24 in Kf.subfield(2 * Kbase.degree()):
            K24 = Kf.subfield(2 * Kbase.degree())
        else:
            K24 = Kf.subfield(3 * Kbase.degree())
            assert f24 in K24
        power = 24
    # Transform polynomial roots x => x**power => cubic(x**power)
    pol = wpoly.monic()
    if power > 1:
        t0 = cputime()
        pol = _fast_adams_operator(pol, power)
        if Kf.degree() > K24.degree():
            verbose(
                f"adams_operator x^{power} reduced field degree {Kf.degree()} => {K24.degree()}",
                t=t0,
            )
            pol = pol.change_ring(K24)
        else:
            verbose(f"adams_operator x^{power}", t=t0)
    if K24 is not Kbase:
        x = polygen(K24)
        t0 = cputime()
        # Apply function (x-16)^3/x
        pol = ((x - 16) ** 3 * x.inverse_mod(pol)).minpoly_mod(pol)
        verbose(
            f"minpoly_mod reduced field degree {K24.degree()} => {Kbase.degree()}", t=t0
        )
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
    Apply transformation x -> x^k to roots of polynomial
    This is equivalent to p.adams_operator(k), but faster.

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
    f = R([newton[k * i] for i in range(1, d + 1)])
    result = (-f).integral().add_bigoh(d + 1).exp(prec=d + 1)
    result = R(result).reverse()
    if _DEBUG:
        assert result == (R.gen() ** k).minpoly_mod(p)
    assert result.degree() == d
    return result


def _fast_pari_roots(poly):
    if not poly.is_squarefree():
        return poly.roots()
    # it's squarefree
    paripoly = poly._pari_with_name()
    R = poly.base_ring()
    return [(R(r), 1) for r in paripoly.polrootsmod()]
