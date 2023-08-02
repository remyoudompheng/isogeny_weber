"""
Binary encoding of the Weber modular polynomial database.

Original files computed by Andrew Sutherland
https://math.mit.edu/~drew/WeberModPolys.html

Expected usage:
    python encode_db.py weber.db phi1.tar.gz
    python encode_db.py --limit 512 weber.db phi1.tar.gz
    python encode_db.py weber.db phi1_*.new.gz
"""
import argparse
import ast
import gzip
import io
import struct
import sys
import tarfile

sys.set_int_max_str_digits(20000)


def encode_coef(dx, dy, a):
    # Fixed size header + variable size integer
    # 1 bit for small vs large
    # Small format:
    # 8 bits for dx, 8 bits for dy, 1 bit for sign, 1 bit for trailing zeros, 5 bits for length
    # Large format:
    # 10 bits for dx, 10 bits for dy
    # 1 bit for sign, 1 bit for trailing zeros, 9 bits for length
    # Very large format (for level above 1024)
    # 16 bits for dx, dy, length, trailing zeros
    l = (abs(a).bit_length() - 1) // 8 + 1
    assert l < 512
    sign = 1 if a < 0 else 0
    abin = abs(a).to_bytes(abs(l), "big")
    # Coefficients are often divisible by a large power of 2.
    tz = len(abin) - len(abin.rstrip(b"\0"))
    assert tz < 256
    if dx < 256 and dy < 256 and l - tz < 32:
        # Small
        hdr = (dx << 15) | (dy << 7) | (sign << 5) | (l - tz)
        if tz:
            hdr |= 1 << 6
            return hdr.to_bytes(3, "big") + bytes([tz]) + abin.rstrip(b"\0")
        else:
            return hdr.to_bytes(3, "big") + abin
    elif dx < 1024 and dy < 1024 and l - tz < 511:
        hdr = (1 << 31) | (dx << 21) | (dy << 11) | (sign << 9) | (l - tz)
        if tz:
            hdr |= 1 << 10
            assert hdr != 0xFFFFFFFF
            return hdr.to_bytes(4, "big") + bytes([tz]) + abin.rstrip(b"\0")
        else:
            return hdr.to_bytes(4, "big") + abin
    else:
        # Large
        hdr = 0xFFFFFFFF
        return struct.pack(">IHHBHH", hdr, dx, dy, sign, l - tz, tz) + abin.rstrip(
            b"\0"
        )


def process_tar(w, tarf, limit=None):
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
        coeffs = []
        for l in mf:
            dxy, a = l.decode().split()
            dx, dy = ast.literal_eval(dxy)
            coeffs.append((dx, dy, int(a)))
        for dx, dy, a in coeffs:
            w.write(encode_coef(dx, dy, a))
        print(mname, w.tell() - off)


def process_file(w, f):
    """
    Process a standalone polynomial file
    """
    for l in f:
        dxy, a = l.decode().split()
        dx, dy = ast.literal_eval(dxy)
        w.write(encode_coef(dx, dy, int(a)))


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
                process_tar(w, tf)
            else:
                off = w.tell()
                with (gzip.open if i.endswith(".gz") else open)(i, "rb") as f:
                    process_file(w, f)
                print(i, w.tell() - off)
