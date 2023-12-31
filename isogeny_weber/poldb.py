"""
Parse binary encoded polynomial database.

Polynomials are deserialized lazily on demand, so that the database
is kept in memory as a single bytestring and consumes as much memory
as the file size.
"""

import struct

from .poldb160 import DB160


def _parse_header(s, off):
    hdr = int.from_bytes(s[off : off + 4], "big")
    large = hdr >> 31
    hdrsize = 3 + large
    if large:
        # Large coefficient
        dx = (hdr >> 24) & 0x7F
        dy = (hdr >> 11) & 0x1FFF
        sgn = (hdr >> 10) & 1
        alen = hdr & 0x3FF
    else:
        # Small coefficient
        hdr >>= 8
        dx = (hdr >> 18) & 31
        dy = (hdr >> 8) & 0x3FF
        sgn = (hdr >> 7) & 1
        alen = hdr & 0x7F
    return hdrsize, dx, dy, sgn, alen


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
            db = DB160
        off = 0
        offs = {}
        while off < len(db):
            # polynomial header
            l = int.from_bytes(db[off : off + 2], "big")
            ncoef = int.from_bytes(db[off + 2 : off + 5], "big")
            poly_start = off
            off += 5
            # coefficients
            for _ in range(ncoef):
                hdrsize, dx, dy, _, alen = _parse_header(db, off)
                assert dy <= l + 1
                off += hdrsize + alen
            offs[l] = (poly_start, off)

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

    def _rawcoeffs(self, l):
        """
        Iterator over raw encoded values
        """
        if l not in self._offs:
            raise ValueError(f"No polynomial for level {l}")
        off, off_end = self._offs[l]
        db = memoryview(self._db)
        _l = int.from_bytes(db[off : off + 2], "big")
        _ncoef = int.from_bytes(db[off + 2 : off + 5], "big")
        assert _l == l
        count = 0
        off += 5
        while off < off_end:
            hdrsize, kdx, dy, sgn, alen = _parse_header(db, off)
            off += hdrsize
            a = int.from_bytes(db[off : off + alen], "big")
            off += alen
            yield kdx, dy, -a if sgn else a
            count += 1
        assert count == _ncoef

    def _coeffs(self, l):
        """
        Expand encoded data to full polynomial integer coefficients
        """
        from sage.all import legendre_symbol, gcd

        yield l, l, -1
        yield l + 1, 0, 1
        yield 0, l + 1, 1
        sign = legendre_symbol(2, l)
        s = gcd(12, (l - 1) // 2)
        # Bottom coefficient
        b = (l - 1) // (2 * s)
        yield 1, 1, -(sign ** (b % 2)) << (b * s)
        for kdx, dy, a in self._rawcoeffs(l):
            a = a * l
            dx = l + 1 - (l * dy) % 24 - 24 * kdx
            assert (l + 1) // 2 <= dx and dx >= dy
            yield dx, dy, a
            # Symmetries
            if dx > dy:
                yield dy, dx, a
            if dx + dy > l + 1:
                lowdx, lowdy = l + 1 - dx, l + 1 - dy
                b = (dx + dy - l - 1) // (2 * s)
                mult = (sign ** (b % 2)) << (b * s)
                yield lowdx, lowdy, mult * a
                if lowdx != lowdy:
                    yield lowdy, lowdx, mult * a

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
        return Zxy(poly)

    def __contains__(self, l):
        return l in self._offs

    def keys(self):
        return self._offs.keys()

    def modular_polynomial(self, l, base_ring=None):
        """
        Returns the Weber modular polynomial of level l
        as a bivariate polynomial over specified ring (or ZZ).
        """
        from sage.rings.all import IntegerRing, PolynomialRing

        R = IntegerRing() if base_ring is None else base_ring
        # Bivariate
        Rxy = PolynomialRing(R, 2, "x,y")
        poly = {}
        for dx, dy, a in self._coeffs(l):
            ra = R(a)
            poly[(dx, dy)] = ra
        return Rxy(poly)

    def instantiate_polynomial(self, l, x):
        """
        Returns the Weber modular polynomial of level l and its 2 partial
        derivatives, instantiated using x for the first variable,
        as univariate polynomials over the parent ring of x.
        """
        R = x.parent()
        Rx = R["x"]
        plist = [R(0) for _ in range(l + 2)]
        plistx = [R(0) for _ in range(l + 2)]
        plisty = [R(0) for _ in range(l + 2)]
        powers = R(x).powers(l + 2)
        for dx, dy, a in self._coeffs(l):
            plist[dx] += a * powers[dy]
            if dx > 0:
                plistx[dx - 1] += (a * dx) * powers[dy]
            if dy > 0:
                plisty[dx] += (a * dy) * powers[dy - 1]
        return Rx(plist), Rx(plistx), Rx(plisty)
