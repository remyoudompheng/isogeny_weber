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


def fast_adams1(p, k):
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


def fast_adams2(p, k):
    # Same as fast_adams1 where exp is computed by Newton iteration
    # See Bostan, Flajolet, Salvy, Schost section 2.2.1
    d = p.degree()
    newton = p.derivative().reverse() * p.reverse().inverse_series_trunc(k * d + 1)
    assert newton[0] == d
    sums = [-newton[k * i] for i in range(1, d + 1)]
    f = p.parent()(sums)
    # Compute F = exp(f) satisfying F' = f' F
    x = p.parent().gen()
    res = 1 + sums[0] * x
    prec = 2
    while prec <= d:
        # m_ is very small
        m_ = f - res.derivative() * res.inverse_series_trunc(2 * prec)
        m = 1 + m_.truncate(2 * prec).integral()
        res = (res * m).truncate(2 * prec)
        prec = 2 * prec
    return res.truncate(d + 1).reverse()


def fast_adams3(p, k):
    x = p.parent().gen()
    return (x**k).minpoly_mod(p)


def fast_adams4(p, k):
    def graeffe2(p):
        # Graeffe transform Q(x²) = (-1)^d P(x)P(-x)
        ps = p.list()
        (x,) = p.variables()
        p_odd = p.parent()(ps[1::2])
        p_even = p.parent()(ps[0::2])
        if p.degree() % 2 == 0:
            return p_even * p_even - x * p_odd * p_odd
        else:
            return x * p_odd * p_odd - p_even * p_even

    def graeffe3(p):
        # Generalized transform
        # Q(x^3) = P(x)P(jx)P(j²x) where j³=1
        # decompose: P = P0(x³) + x P1(x³) + x² P2(x³)
        # Then Q(x^3) = P0^3 + x P1^3 + x^2 P2^3 - 3 x P0 P1 P2
        ps = p.list()
        (x,) = p.variables()
        p0 = p.parent()(ps[0::3])
        p1 = p.parent()(ps[1::3])
        p2 = p.parent()(ps[2::3])
        return p0**3 + x * p1**3 + x**2 * p2**3 - 3 * x * p0 * p1 * p2

    assert p.is_monic()
    while k % 2 == 0:
        p = graeffe2(p)
        k //= 2
    while k % 3 == 0:
        p = graeffe3(p)
        k //= 3
    assert p.is_monic()
    return p


def main(bits, e, d, k):
    print(f"=> GF(p{bits}^{e}), polynomial degree {d}, Graeffe/Adams transform x^{k}")
    p = random_prime(2**bits, lbound=2 ** (bits - 1))
    Kx = PolynomialRing(GF((p, e), "g"), "x")
    pol = Kx.random_element(d).monic()
    # Fast
    t = cputime()
    q = fast_adams1(pol, k)
    print(f"newton sum  {cputime(t):.3f}s")
    assert q.degree() == pol.degree(), (pol.degree(), q.degree())
    assert q.is_monic()
    # Fast composite
    if k == 24:
        t = cputime()
        qc = fast_adams1(fast_adams1(pol, 4), 6)
        assert q == qc
        print(f"newton 4x6  {cputime(t):.3f}s")
    # Custom exp
    t = cputime()
    qc = fast_adams2(pol, k)
    assert q == qc
    print(f"newton sum2 {cputime(t):.3f}s")
    # Using Shoup's minpoly
    t = cputime()
    q2 = fast_adams3(pol, k)
    print(f"minpoly mod {cputime(t):.3f}s")
    assert q2.degree() == pol.degree(), (pol.degree(), q2.degree())
    assert q2.is_monic()
    assert q == q2
    # Using Graeffe transform formulas
    t = cputime()
    q4 = fast_adams4(pol, k)
    print(f"graeffe     {cputime(t):.3f}s")
    assert q == q4
    # Adams
    if p.bit_length() < 29:
        t = cputime()
        pk = pol.adams_operator(k)
        print(f"resultant   {cputime(t):.3f}s")
        assert pk == q
    # Roots
    if bits * e <= 1024:
        t = cputime()
        q = pol._pari_with_name().polrootsmod()
        print(f"pariroots   {cputime(t):.3f}s")
        t = cputime()
        q = pol.roots()
        print(f"roots       {cputime(t):.3f}s")


if __name__ == "__main__":
    proof.arithmetic(False)
    for degree in (100, 200, 400, 800):
        for pbits in (30, 64, 128, 256, 800):
            # Don't benchmark prime fields
            # main(pbits, 1, degree, 24)
            main(pbits, 3, degree, 3)
            main(pbits, 6, degree, 6)
            main(pbits, 12, degree, 12)
            main(pbits, 24, degree, 24)
