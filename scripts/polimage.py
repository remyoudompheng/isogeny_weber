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

# Now apply operator x -> (x-16)^3-jx
def fast_adams3(p, k):
    x = p.parent().gen()
    return (x**k).minpoly_mod(p)

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
            #main(pbits, 1, degree, 24)
            main(pbits, 3, degree, 3)
            main(pbits, 6, degree, 6)
            main(pbits, 12, degree, 12)
            main(pbits, 24, degree, 24)

