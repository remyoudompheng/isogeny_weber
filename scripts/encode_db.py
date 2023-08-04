r"""
Binary encoding of the Weber modular polynomial database.

Original files computed by Andrew Sutherland
https://math.mit.edu/~drew/WeberModPolys.html

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
  - they are multiples of l
  - total degree d = (l+1) ± 2bs and degree=[d/2±ar,d/2∓ar]
    where r = gcd(12, (l+1)/2) and s = gcd(12, (l-1)/2)
  - if degree is [dx,dy] then
    l*dx+dy = dx+l*dy = l+1 mod 24

- variable symmetry (horizontal):
  coefficients [d/2+ar,d/2-ar] and [d/2-ar,d/2+ar] are equal

- reciprocal symmetry (vertical):
  coefficients c+ = [(l+1)/2+dx,(l+1)/2+dy]
  and c- = [(l+1)/2-dx,(l+1)/2-dy]
  with total degree l+1+bs and l+1-bs
  are such that c- = (±2)^bs when the sign is given by
  the Legendre symbol (2|l)
  Usually c+ has low 2-valuation.

So we only encode:
- coefficients with total degree l+1 <= dx+dy < 2l
- such that dx >= dy (upper left quadrant), in particular dx >= (l+1)/2
- coefficients are divided by l
- dx is stored as K such that dx = l+1 - (l*dy) % 24 - 24K
  K is at most (l+1) / 48
- dy is stored unchanged

Expected usage:
    python encode_db.py weber.db phi1.tar.gz
    python encode_db.py --limit 512 weber.db phi1.tar.gz
    python encode_db.py weber.db phi1_*.new.gz
"""
import argparse
import ast
import gmpy2
import gzip
import io
import math
import sys
import tarfile

sys.set_int_max_str_digits(20000)


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
        return hdr.to_bytes(3, "big") + abin
    else:
        # Large
        assert dx < 128
        assert dy < 8192
        assert sz < 1024
        hdr = (1 << 31) | (dx << 24) | (dy << 11) | (sign << 10) | sz
        return hdr.to_bytes(4, "big") + abin


def read_polynomial(r):
    coeffs = []
    for l in r:
        dxy, a = l.decode().split()
        dx, dy = ast.literal_eval(dxy)
        coeffs.append((dx, dy, int(a)))
    # Sort by decreasing total degree and degree of x
    coeffs.sort(key=lambda v: (-v[0] - v[1], -v[0]))
    return coeffs


def check_properties(coeffs, l):
    sign = gmpy2.legendre(2, l)
    s = math.gcd(12, (l - 1) // 2)
    d = {(dx, dy): c for dx, dy, c in coeffs}
    for (dx, dy), c in d.items():
        if (dx, dy) == (l + 1, 0):
            assert c == 1
            continue
        elif (dx, dy) == (l, l):
            assert c == -1
            continue
        elif (dx, dy) == (1, 1):
            # Mirror of (l,l)
            b = (l - 1) // (2 * s)
            assert c == -((sign * 2**s) ** b)
            continue
        assert 2 < dx + dy < l + l
        assert dx <= l and dy <= l
        assert c % l == 0
    for (dx, dy), c in d.items():
        if dx + dy > l + 1:
            assert dx >= (l + 1) // 2
            assert l - dx <= (l - 1) // 2
            bs = dx + dy - (l + 1)
            b = bs // (2 * s)
            assert d[l + 1 - dy, l + 1 - dx] == (sign * 2**s) ** b * c


def filter_poly(coeffs, l):
    """
    Remove/reduce redundant coefficients for compression
    """
    lp1_24 = (l + 1) % 24
    for dx, dy, c in coeffs:
        if l + 1 <= dx + dy < 2 * l and dx <= l and dy <= l:
            assert c % l == 0
            assert (l * dx + dy) % 24 == lp1_24
            assert (dx + l * dy) % 24 == lp1_24
            K = (l + 1 - (l * dy) % 24 - dx) // 24
            assert dx == l + 1 - (l * dy) % 24 - 24 * K
            yield K, dy, c // l


def dump_poly(w, coeffs, l):
    hdr = l.to_bytes(2, "big") + len(coeffs).to_bytes(3, "big")
    w.write(hdr)
    for dx, dy, a in coeffs:
        w.write(encode_coef(dx, dy, a))


def process_tar(w, tf, limit=None):
    """
    Process a tarball like
    https://math.mit.edu/~drew/webermodpoly/phi1.tar.gz
    """
    fnames = []
    for m in tf.getmembers():
        if "." not in m.name:
            continue
        _, _, ext = m.name.partition("phi1_")
        ell = int(ext.partition(".")[0])
        fnames.append((ell, m.name))
    for ell, mname in sorted(fnames):
        if limit and ell > limit:
            break
        off = w.tell()
        mf = tf.extractfile(mname)
        coeffs = read_polynomial(mf)
        check_properties(coeffs, ell)
        coeffs = list(filter_poly(coeffs, ell))
        dump_poly(w, coeffs, ell)
        print(mname, w.tell() - off, "coefficients", len(coeffs))


def process_file(w, f):
    """
    Process a standalone polynomial file
    """
    coeffs = read_polynomial(f)
    l = max(coeffs)[0] - 1
    check_properties(coeffs, l)
    coeffs = list(filter_poly(coeffs, l))
    dump_poly(w, coeffs, l)
    return len(coeffs)


if __name__ == "__main__":
    argp = argparse.ArgumentParser()
    argp.add_argument("--limit", default=None, type=int)
    argp.add_argument("OUTPUT")
    argp.add_argument("INPUT", nargs="+")
    args = argp.parse_args()

    with open(args.OUTPUT, "wb") as w:
        for i in args.INPUT:
            if i.endswith(".tar.gz"):
                tf = tarfile.TarFile(fileobj=io.BytesIO(gzip.GzipFile(i).read()))
                process_tar(w, tf, limit=args.limit)
            else:
                off = w.tell()
                with (gzip.open if i.endswith(".gz") else open)(i, "rb") as f:
                    n = process_file(w, f)
                print(i, w.tell() - off, "coefficients", n)
