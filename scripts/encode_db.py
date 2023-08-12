r"""
Transcoding utility for the Weber modular polynomial database.

Original files computed by Andrew Sutherland
https://math.mit.edu/~drew/WeberModPolys.html

Output files should be 40% of original size.

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
from isogeny_weber import poldb_encode

sys.set_int_max_str_digits(20000)


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
        n = poldb_encode.encode_poly(w, coeffs, ell)
        print(mname, w.tell() - off, "coefficients", n)


def process_file(w, f):
    """
    Process a standalone polynomial file
    """
    coeffs = read_polynomial(f)
    l = max(coeffs)[0] - 1
    check_properties(coeffs, l)
    n = poldb_encode.encode_poly(w, coeffs, l)
    return n


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
