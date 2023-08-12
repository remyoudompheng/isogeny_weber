"""
Extra FLINT ARB bindings for interpolation of real polynomials
"""

from cysignals.memory cimport sig_malloc, sig_free
from cysignals.signals cimport sig_on, sig_off
from sage.libs.arb.acb cimport acb_set, _acb_vec_init, _acb_vec_clear
from sage.libs.arb.acb_poly cimport acb_poly_product_roots
from sage.libs.arb.arb cimport arb_set
from sage.libs.arb.types cimport acb_ptr, acb_srcptr, acb_struct, arb_srcptr, arb_ptr, arb_poly_t, arb_t
from sage.rings.complex_arb cimport ComplexBall
from sage.rings.real_arb cimport RealBall
from sage.rings.polynomial.polynomial_complex_arb cimport Polynomial_complex_arb
from sage.rings.all import ComplexBallField

cdef extern from "arb_wrap.h":
    arb_ptr _arb_vec_init(long n)
    void _arb_vec_clear(arb_ptr v, long n)

    void arb_poly_init(arb_poly_t poly)
    void arb_poly_clear(arb_poly_t poly)
    void arb_poly_get_coeff_arb(arb_t v, const arb_poly_t poly, long n)
    void arb_poly_product_roots_complex(arb_poly_t poly, arb_srcptr r, long rn, acb_srcptr c, long cn, long prec)
    void arb_poly_interpolate_fast(arb_poly_t poly, arb_srcptr xs, arb_srcptr ys, long n, long prec)

def rx_interpolate(xs, ys):
    """
    Returns the Lagrange interpolation polynomials
    for a list of points (x,y)
    """
    assert all(isinstance(r, RealBall) for r in xs)
    assert all(isinstance(r, RealBall) for r in ys)
    cdef int n = len(xs)
    assert len(ys) == n
    RR = xs[0].parent()
    prec = RR.prec()
    cdef arb_poly_t poly
    arb_poly_init(poly)
    cdef arb_ptr rxs = _arb_vec_init(n)
    cdef arb_ptr rys = _arb_vec_init(n)
    for i from 0 <= i < n:
        arb_set(&rxs[i], (<RealBall>xs[i]).value)
        arb_set(&rys[i], (<RealBall>ys[i]).value)
    sig_on()
    arb_poly_interpolate_fast(poly, rxs, rys, n, prec)
    sig_off()
    _arb_vec_clear(rxs, n)
    _arb_vec_clear(rys, n)
    # Format result
    result = []
    cdef RealBall coef
    for i from 0 <= i <= n:
        coef = RealBall.__new__(RealBall)
        coef._parent = RR
        arb_poly_get_coeff_arb(coef.value, poly, i)
        result.append(coef)
    arb_poly_clear(poly)
    return RR["x"](result)

def rx_from_roots(roots, croots):
    """
    Return a RealBall polynomial having real roots `roots`
    and complex root pairs `croots`

    roots must be non-empty.
    """
    assert all(isinstance(r, RealBall) for r in roots)
    assert all(isinstance(c, ComplexBall) for c in croots)
    RR = roots[0].parent()
    prec = RR.prec()
    cdef arb_poly_t poly
    arb_poly_init(poly)
    cdef int nr = len(roots)
    cdef int nc = len(croots)
    cdef arb_ptr rs = _arb_vec_init(nr)
    cdef acb_ptr cs = _acb_vec_init(nc)
    for i from 0 <= i < nr:
        arb_set(&rs[i], (<RealBall>roots[i]).value)
    for i from 0 <= i < nc:
        acb_set(&cs[i], (<ComplexBall>croots[i]).value)
    sig_on()
    arb_poly_product_roots_complex(poly, rs, nr, cs, nc, prec);
    sig_off()
    result = []
    cdef RealBall coef
    for i from 0 <= i < nr + 2 * nc:
        coef = RealBall.__new__(RealBall)
        coef._parent = RR
        arb_poly_get_coeff_arb(coef.value, poly, i)
        result.append(coef)
    result.append(RR(1))
    _arb_vec_clear(rs, nr)
    _acb_vec_clear(cs, nc)
    arb_poly_clear(poly)
    return RR["x"](result)

def cx_from_roots(croots):
    "Returns the monic ComplexBall polynomial with specified roots"
    assert all(isinstance(r, ComplexBall) for r in croots)
    CC = croots[0].parent()
    prec = CC.prec()
    poly = (<Polynomial_complex_arb> CC["x"].gen())._new()
    n = len(croots)
    cdef acb_ptr rs = _acb_vec_init(n)
    for i from 0 <= i < n:
        acb_set(&rs[i], (<ComplexBall>croots[i]).value)
    sig_on()
    acb_poly_product_roots((<Polynomial_complex_arb>poly).__poly, <acb_srcptr>rs, n, prec)
    sig_off()
    _acb_vec_clear(rs, n)
    return poly
