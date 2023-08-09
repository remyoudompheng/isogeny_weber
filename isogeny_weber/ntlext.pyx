# distutils: libraries = NTL_LIBRARIES gmp m
# distutils: extra_compile_args = NTL_CFLAGS
# distutils: include_dirs = NTL_INCDIR
# distutils: library_dirs = NTL_LIBDIR
# distutils: extra_link_args = NTL_LIBEXTRA
# distutils: language = c++

"""
Additional NTL library bindings missing from Sage.
"""

from cysignals.signals cimport sig_on, sig_off

from sage.rings.integer cimport Integer
from sage.libs.ntl.ntl_ZZ_p cimport ntl_ZZ_p
from sage.libs.ntl.types cimport ZZ_pX_Modulus_c, ZZ_pContext_c
from sage.libs.ntl.ZZ_pX cimport ZZ_pX_CompMod, ZZ_pX_PowerMod_pre, ZZ_pX_PowerXMod_pre, ZZ_pX_Modulus_build
from sage.libs.ntl.ntl_ZZ cimport ntl_ZZ
from sage.libs.ntl.ntl_ZZ_pX cimport ntl_ZZ_pX, ntl_ZZ_pX_Modulus

def xpow(n, ntl_ZZ_pX modulus):
    "Computes X^n modulo modulus"
    cdef ntl_ZZ nz = ntl_ZZ(n)
    cdef ntl_ZZ_pX r = modulus._new()
    cdef ZZ_pX_Modulus_c mod
    ZZ_pX_Modulus_build(mod, modulus.x)
    sig_on()
    ZZ_pX_PowerXMod_pre(r.x, nz.x, mod)
    sig_off()
    return r

def powmod(ntl_ZZ_pX self, n, ntl_ZZ_pX modulus):
    "Modular exponentiation pow(self, n, modulus)"
    if self.c is not modulus.c:
        raise ValueError("You cannot perform arithmetic with elements of different moduli.")
    cdef ntl_ZZ nz = ntl_ZZ(n)
    cdef ntl_ZZ_pX r = modulus._new()
    cdef ZZ_pX_Modulus_c mod
    ZZ_pX_Modulus_build(mod, modulus.x)
    sig_on()
    ZZ_pX_PowerMod_pre(r.x, self.x, nz.x, mod)
    sig_off()
    return r

def compmod(ntl_ZZ_pX f, ntl_ZZ_pX g, ntl_ZZ_pX modulus):
    "Modular composition f(g) mod Modulus"
    if f.c is not modulus.c or g.c is not modulus.c:
        raise ValueError("You cannot perform arithmetic with elements of different moduli.")
    cdef ntl_ZZ_pX r = modulus._new()
    cdef ZZ_pX_Modulus_c mod
    ZZ_pX_Modulus_build(mod, modulus.x)
    sig_on()
    ZZ_pX_CompMod(r.x, f.x, g.x, mod)
    sig_off()
    return r
   

