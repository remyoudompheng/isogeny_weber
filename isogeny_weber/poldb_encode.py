r"""
Binary encoding of the Weber modular polynomial database.

The Weber modular polynomials obey symmetries corresponding
to the Schläfli modular equations.

                 (l,l)
                       /\ total degree
    (l+1,0)            ||   (0,l+1)

     <-- deg(x)  (1,1)   deg(y) -->


Coefficients satisfy:
- [l+1,0] = 1
- [l,l] = -1
- all middle coefficients (total degree 2..2l-1 and each degree <= l)
  are such that:
  - they are multiples of l (Kronecker congruence)
  - total degree d = (l+1) ± 2bs and degree=[d/2±ar,d/2∓ar]
    where r = gcd(12, (l+1)/2) and s = gcd(12, (l-1)/2)
  - if degree is [dx,dy] then
    l*dx+dy = dx+l*dy = l+1 mod 24

- variable symmetry (horizontal):
  coefficients [d/2+ar,d/2-ar] and [d/2-ar,d/2+ar] are equal

- reciprocal symmetry (vertical):
  coefficients c+ = [(l+1)/2+dx,(l+1)/2+dy]
  and c- = [(l+1)/2-dx,(l+1)/2-dy]
  with total degree l+1+2bs and l+1-2bs
  are such that c- = (±2^s)^b when the sign is given by
  the Legendre symbol (2|l)
  Usually c+ has low 2-valuation.

So we only encode:
- coefficients with total degree l+1 <= dx+dy < 2l
- such that dx >= dy (upper left quadrant), in particular dx >= (l+1)/2
- coefficients are divided by l
- dx is stored as K such that dx = l+1 - (l*dy) % 24 - 24K
  K is at most (l+1) / 48
- dy is stored unchanged
"""


def encode_poly(w, coeffs, l):
    # Sort by decreasing total degree and degree of x
    coeffs.sort(key=lambda v: (-v[0] - v[1], -v[0]))
    coeffs = list(filter_poly(coeffs, l))
    hdr = int(l).to_bytes(2, "big") + len(coeffs).to_bytes(3, "big")
    w.write(hdr)
    for dx, dy, a in coeffs:
        w.write(encode_coef(dx, dy, int(a)))
    return len(coeffs)


def encode_coef(dx, dy, a):
    # Header (3-4 bytes) + variable size integer
    # Small format (l <= 1024, coefficients smaller than 1024 bits):
    # MSB=0 5 bits for K(dx) < 31, 10 bits for dy, 1 bit for sign, 7 bits for length
    # Large format (l <= 5000, possibly l <= 6000, coeff < 8000 bits)
    # MSB=1 7 bits for dx, 13 bits for dy, 1 bit for sign, 10 bits for length
    sz = (abs(a).bit_length() - 1) // 8 + 1
    sign = 1 if a < 0 else 0
    abin = abs(a).to_bytes(sz, "big")
    if dx < 31 and dy < 1024 and sz < 128:
        # Small
        hdr = (dx << 18) | (dy << 8) | (sign << 7) | sz
        assert hdr >> 31 == 0
        return int(hdr).to_bytes(3, "big") + abin
    else:
        # Large
        assert dx < 128
        assert dy < 8192
        assert sz < 1024
        hdr = (1 << 31) | (dx << 24) | (dy << 11) | (sign << 10) | sz
        return int(hdr).to_bytes(4, "big") + abin


def filter_poly(coeffs, l):
    """
    Remove/reduce redundant coefficients for compression

    Only dx >= dy is kept
    Only dx + dy >= l + 1 is kept
    Coefficients (l+1,0), (0,l+1), (l,l) are removed
    """
    lp1_24 = (l + 1) % 24
    for dx, dy, c in coeffs:
        if c and dx >= dy and l + 1 <= dx + dy < 2 * l and dx <= l and dy <= l:
            assert c % l == 0
            assert (l * dx + dy) % 24 == lp1_24
            assert (dx + l * dy) % 24 == lp1_24
            K = (l + 1 - (l * dy) % 24 - dx) // 24
            assert dx == l + 1 - (l * dy) % 24 - 24 * K
            yield K, dy, c // l
