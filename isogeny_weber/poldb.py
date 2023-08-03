"""
Parse binary encoded polynomial database.

Polynomials are deserialized lazily on demand, so that the database
is kept in memory as a single bytestring and consumes as much memory
as the file size.
"""

import struct

from .poldb128 import DB128


def _parse_header(s, off):
    hdr = int.from_bytes(s[off : off + 4], "big")
    large = hdr >> 31
    hdrsize = 3 + large
    if hdr == 0xFFFFFFFF:
        # Very large coefficient
        hdrsize = 13
        dx, dy, sgn, alen, tz = struct.unpack(">HHBHH", s[off + 4 : off + 13])
    elif large:
        # Large coefficient
        dx = (hdr >> 21) & 0x3FF
        dy = (hdr >> 11) & 0x3FF
        tz = (hdr >> 10) & 1
        sgn = (hdr >> 9) & 1
        alen = hdr & 0x1FF
        if tz:
            tz = s[off + hdrsize]
            hdrsize += 1
    else:
        # Small coefficient
        hdr >>= 8
        dx = (hdr >> 15) & 0xFF
        dy = (hdr >> 7) & 0xFF
        tz = (hdr >> 6) & 1
        sgn = (hdr >> 5) & 1
        alen = hdr & 31
        if tz:
            tz = s[off + hdrsize]
            hdrsize += 1
    return hdrsize, dx, dy, tz, sgn, alen


class Database:
    def __init__(self, filename=None):
        """
        Load a Weber modular polynomial database from a file,
        or load hardcoded database for 5 <= l <= 127 if not specified.
        """
        if filename is not None:
            with open(filename, "rb") as f:
                db = f.read()
        else:
            db = DB128
        off = 0
        offs = {}
        l = None
        while off < len(db):
            hdrsize, dx, dy, tz, sgn, alen = _parse_header(db, off)
            # Each polynomial starts with a leading coefficient X^(l+1)
            # and ends with a coefficient [1,1]
            if dy == 0:
                l = dx - 1
                offs[l] = (off, None)
            if dx == 1 and dy == 1:
                offs[l] = (offs[l][0], off + hdrsize + alen)
            off += hdrsize + alen

        self._db = db
        self._offs = offs
        try:
            from sage.misc.verbose import verbose

            minl, maxl = min(offs), max(offs)
            verbose(
                f"Read polynomial database from {filename} (size {off} levels {minl}..{maxl})"
            )
        except ImportError:
            pass

    def _coeffs(self, l):
        if l not in self._offs:
            raise ValueError(f"No polynomial for level {l}")
        off, off_end = self._offs[l]
        db = memoryview(self._db)
        while off < off_end:
            hdrsize, dx, dy, tz, sgn, alen = _parse_header(db, off)
            off += hdrsize
            a = int.from_bytes(db[off : off + alen], "big")
            if tz:
                a <<= 8 * tz
            off += alen
            yield dx, dy, -a if sgn else a

    def __getitem__(self, l):
        """
        Returns the Weber modular polynomial of level 1
        as an element of ZZ[x,y]
        """
        from sage.rings.all import IntegerRing, PolynomialRing

        Zxy = PolynomialRing(IntegerRing(), 2, "x,y")
        poly = {}
        for dx, dy, a in self._coeffs(l):
            poly[(dx, dy)] = a
            poly[(dy, dx)] = a
        return Zxy(poly)

    def keys(self):
        return self._offs.keys()

    def modular_polynomial(self, l, base_ring=None, y=None):
        """
        Returns the Weber modular polynomial of level l
        optionally specialized for a given coefficient ring
        or for a numerical value of the y variable.
        """
        from sage.rings.all import IntegerRing, PolynomialRing

        R = IntegerRing() if base_ring is None else base_ring
        if y is None:
            # Bivariate
            Rxy = PolynomialRing(R, 2, "x,y")
            poly = {}
            for dx, dy, a in self._coeffs(l):
                ra = R(a)
                poly[(dx, dy)] = ra
                poly[(dy, dx)] = ra
            return Rxy(poly)
        else:
            # Univariate
            Rx = PolynomialRing(R, "x")
            coeffs = [R(0) for _ in range(l + 2)]
            powers = R(y).powers(l + 2)
            for dx, dy, a in self._coeffs(l):
                coeffs[dx] += a * powers[dy]
                if dx != dy:
                    coeffs[dy] += a * powers[dx]
            return Rx(coeffs)
