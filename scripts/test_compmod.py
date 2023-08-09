"""
Benchmark for modular exponentiation implementations.
"""

from sage.all import GF, random_prime, pari, cputime, ZZ
from isogeny_weber.polynomials import (
    frobenius_mod,
    modular_composition,
    modular_automorphism,
)

for psize in range(250, 2000, 250):
    for deg in range(100, 1000, 200):
        if deg > psize:
            break
        print(f"Prime size {psize} bits")
        print(f"Modulus degree = {deg}")

        p = random_prime(2**psize, lbound=2 ** (psize - 1))
        K, Kx = GF(p), GF(p)["x"]
        x = Kx.gen()
        a, b = K.random_element(), K.random_element()
        h = Kx.random_element(deg)

        phi = frobenius_mod(h, p)

        t0 = cputime()
        phi2a = modular_automorphism(h, phi)(phi)
        print(f"Hand-made Frob(Frob) mod h computed in {cputime(t0):.3f}s")

        t0 = cputime()
        phi2b = modular_composition(phi, phi, h)
        print(f"NTL Frob(Frob) mod h computed in {cputime(t0):.3f}s")
        assert phi2a == phi2b
