"""
Check implementation of torsion polynomials in quotient rings.
"""

from sage.all import *
from isogeny_weber.isogenies import EllMultiples

for _ in range(1000):
    K = GF(random_prime(2**64))
    A = K.random_element()
    B = K.random_element()
    x = polygen(K)
    Kx = x.parent()
    modulus = x**500 + 1
    E = EllipticCurve(K, [A, B])
    # scalars
    P = E.random_point()
    EM = EllMultiples(x, 100, A, B, Kx(P[0]))
    for l in range(1, 100):
        Pl = ZZ(l) * P
        assert Pl.xy() == (EM.x(l), EM.y(l, Kx(P[1])))
    # polynomials
    EM = EllMultiples(modulus, 100, A, B, x)
    for l in range(1, 100):
        P1 = E.division_polynomial_0(l, x) % modulus
        P2 = EM.psi(l) % modulus
        assert P1 == P2
    print(E, "OK")
