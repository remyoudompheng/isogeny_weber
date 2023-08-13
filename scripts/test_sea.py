"""
Test cases for SEA implementation (for observed bugs)

All curves are y^2 = x^3 + 123 x + 456
for varying primes p.
"""

from sage.all import EllipticCurve, GF
from isogeny_weber import trace_of_frobenius


def test_123456(p, t):
    E = EllipticCurve(GF(p), [123, 456])
    tr = trace_of_frobenius(E)
    assert tr == t, tr
    print("OK", E)


# Small field: wrong ring for polynomial descent
# Incorrect trace for l=7
# The modular polynomial factors have degree 6 over GF(p),
# not 2 (over GF(p^3))
test_123456(541594654084139, 16919169)

# Small field: wrong ring for modular equation
# Equation for l=19 is irreducible (degree 20)
test_123456(835411555682621, 6054900)

# Small field: wrong ring for polynomial descent
# More examples
test_123456(870712178977, -1459388)
test_123456(4508409571411, -3731740)

# No Atkin prime, negative trace
# CRT must select the negative candidate.
test_123456(1217, -33)

# Sage CRT arguments must be Sage integers
test_123456(1439, 8)

# Isogenous to (non supersingular) j=0
test_123456(439, 41)
test_123456(709, -31)

# j=1728
test_123456(19, 0)

# Over GF(10009), j=3552 has 2 distinct 17-isogenies to j=5562
# but this is not a singular point on the Weber modular curve.
# This means multiple preimages when lifting roots via x^24
# The discriminant is -2D^2
test_123456(10009, 106)

# Over GF(9001), j=2709 has 2 distinct 17-isogenies to j=936
# but this is not a singular point on the Weber modular curve.
# This means multiple preimages when lifting roots via (x^24-16)^3-jx^24
test_123456(9001, -127)

# Duplicate isogenies for l=5, 13, 17...
# The discriminant is -D^2
test_123456(3733, -44)

# Fails a sanity check: product(primes(5, bit_length)) >= 4 sqrt(p)
test_123456(557125316788065911, 269768565)
