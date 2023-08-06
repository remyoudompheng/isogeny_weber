"""
Test patterns of roots of (x^24 - 16)^3 - j x^24

If (X - 16)^3 - jX is irreducible over the field of definition of j,
then X has a 24-th root in the corresponding cubic extension.
"""

from sage.all import random_prime, GF, polygen, proof, cputime

BITS = 48

proof.arithmetic(False)

def test_finvariants():
    for deg in (1, 2, 3):
        print(f"Base field GF(p^{deg})")
        t = cputime()
        N = 100
        irr = 0
        for _ in range(N):
            p = random_prime(2**BITS)
            K = GF((p, deg), "g")
            j = K.random_element()
            x = polygen(K)
            cubic = (x - 16) ** 3 - j * x
            if cubic.is_irreducible():
                # 1/3 probability
                K3 = K.extension(3, "z")
                f24 = cubic.roots(ring=K3)[0][0]
                # The 24-th root always exists
                assert f24.nth_root(24)
                irr += 1
            else:
                # It has a root, so f^24 is in the base field.
                r = cubic.roots()[0][0]
                pass
        print(f"tested {N} j, {irr} irreducible cubics in {cputime(t):.3f}s")

if __name__ == "__main__":
    main()
