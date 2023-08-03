"""
Benchmark for several methods to apply a power operator to polynomial roots

These operator are used to reduce extension degree of coefficients.
The running time of degree reduction is compared to the time for computing
roots on that base field.

Reference:
https://doi.org/10.1016/j.jsc.2005.07.001
Fast computation of special resultants
Bostan, Flajolet, Salvy, Schost
"""

from sage.all import *


def fast_adams(p, k):
    assert p.is_monic()
    # Same as p.adams_operator(24)
    # The i-th Newton sums of roots of p1(y)
    # is the 24i-th Newton sum of p(x)
    # Compute prev'/prev and extract coefficients
    d = p.degree()
    newton = p.derivative().reverse() * p.reverse().inverse_series_trunc(k * d + 1)
    assert newton[0] == d
    # Reconstruction polynomial from Newton sums
    # exp(integral (d - newton)/x)
    # and reverse coefficients again
    sums = [newton[k * i] for i in range(1, d + 1)]
    f = p.parent()(sums)
    result = (-f).integral().add_bigoh(d + 1).exp(prec=d + 1)
    return p.parent()(result).reverse()


# Now apply operator x -> (x-16)^3-jx
def fast_adams2(p):
    x = p.parent().gen()
    return (x**24).minpoly_mod(p)


def main(bits, e, d):
    print(f"p{bits}^{e}, degree {d}")
    p = random_prime(2 ** (bits - 1), 2**bits)
    Kx = PolynomialRing(GF((p, e), "g"), "x")
    pol = Kx.random_element(d).monic()
    # Fast
    t = cputime()
    q = fast_adams(pol, 24)
    print(f"newton sum {cputime(t):.6f}s")
    assert q.degree() == pol.degree(), (pol.degree(), q.degree())
    assert q.is_monic()
    # Fast composite
    t = cputime()
    qc = fast_adams(fast_adams(pol, 4), 6)
    assert q == qc
    print(f"newton 4x6 {cputime(t):.6f}s")
    # Fast 2
    t = cputime()
    q2 = fast_adams2(pol)
    print(f"minpoly mod {cputime(t):.6f}s")
    assert q2.degree() == pol.degree(), (pol.degree(), q2.degree())
    assert q2.is_monic()
    assert q == q2
    # Adams
    if p.bit_length() < 32:
        t = cputime()
        p24 = pol.adams_operator(24)
        print(f"resultant {cputime(t):.6f}s")
        assert p24 == q
    # Roots
    t = cputime()
    q = pol._pari_with_name().polrootsmod()
    print(f"pariroots {cputime(t):.6f}s")
    t = cputime()
    q = pol.roots()
    print(f"roots {cputime(t):.6f}s")


main(30, 1, 400)
main(30, 6, 400)
main(30, 24, 400)
main(64, 1, 400)
main(64, 6, 400)
main(64, 24, 400)
main(65, 1, 400)
main(65, 6, 400)
main(65, 24, 400)
main(256, 1, 400)
main(256, 6, 400)
main(256, 24, 400)
