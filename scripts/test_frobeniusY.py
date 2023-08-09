"""
Benchmark for modular exponentiation implementations.
"""

from sage.all import GF, random_prime, pari, cputime, ZZ
from isogeny_weber.polynomials import powmod_ntl

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

        F = x**3 + a * x + b

        t0 = cputime()
        fp = pow(F, (p - 1) // 2, h)
        print(f"Sage F^(p-1)/2 mod h computed in {cputime(t0):.3f}s")

        t0 = cputime()
        fpN = powmod_ntl(F, (p - 1) // 2, h)
        print(f"NTL F^(p-1)/2 mod h computed in {cputime(t0):.3f}s")
        assert fp == fpN

        t0 = cputime()
        fp_pari = pari.Mod(F._pari_with_name(), h._pari_with_name()) ** ((p - 1) // 2)
        print(f"PARI F^(p-1)/2 mod h computed in {cputime(t0):.3f}s")
        assert fp == Kx(fp_pari.lift())
