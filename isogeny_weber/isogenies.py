"""
Compute isogenies of a given prime degree l using Weber modular
polynomials.
"""

from sage.all import ZZ, EllipticCurve, polygen
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
    Kext = K.extension(eqf2, "f")
    f = eqf2.any_root(ring=Kext)
    verbose(f"f-invariant {f} in field {Kext}")
    wp = weber_db.modular_polynomial(l, base_ring=Kext, y=f)
    verbose(f"modular equation {wp}")
    for f2, mult in _fast_pari_roots(wp):
        f2_24 = f2**24
        j2 = (f2_24 - 16) ** 3 / f2_24
        if j2 not in K:
            continue
        verbose(f"root {f2} yields codomain j={j2}")
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
            jj2 = -phix * jj / (l * phiy)
            mm = jj2 / j2
            kk = jj2 / (1728 - j2)
            E2 = EllipticCurve(K, [l**4 * mm * kk / 48, l**6 * mm**2 * kk / 864])
            assert E2.j_invariant() == j2
            ker = compute_isogeny_kernel_polynomial(E, E2, l)
            yield E.isogeny(ker, codomain=E2, degree=l)


def _fast_pari_roots(poly):
    if not poly.is_squarefree():
        return poly.roots()
    # it's squarefree
    paripoly = poly._pari_with_name()
    R = poly.base_ring()
    return [(R(r), 1) for r in paripoly.polrootsmod()]
