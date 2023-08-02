# Computation of isogenies using Weber modular polynomials

This library implements a computation of isogenies
similar to SageMath `isogenies_prime_degree`
using Weber modular polynomials, following the methods and formulas
found in:

Andrew V. Sutherland, On the evaluation of modular polynomials,
ANTS X, 2013 [arXiv/1202.3985](https://arxiv.org/abs/1202.3985)

See also:

Steven Galbraith, Mathematics of public key cryptography, chapter 25
https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html

This script is a hobby project and is not meant to be used
in any serious research or computation.

# Database footprint

The Weber modular polynomials are known to use much less
space than classical modular polynomials (about 1728x less space).

An ad-hoc binary encoding is used to store Weber modular
polynomials in a space-efficient way. The resulting files
are smaller than gzipped files available at
https://math.mit.edu/~drew/WeberModPolys.html
and standard compression algorithms will not reduce their size
further.

This is achieved by storing coefficients in binary format
and trimming trailing zero bits. The polynomial database
for `l < 512` uses 3.6MB of disk or memory, compared to
27MB for the SageMath `database_kohel` package
(classical modular polynomials for `l <= 113`, bzip2 compressed)
or `40MB` for the PARI seadata database (Atkins modular polynomials
for `l < 500`, uncompressed).

The precomputed degrees up to 1000 use 73MB of disk/memory
(original file size 91MB) and degrees between 1000 and 2048
would use 1188MB (original file size 1439MB).

# Performance

This implementation is usually much faster than the generic
implementation of `isogenies_prime_degree` factoring torsion
polynomials (but slower than the optimized versions
used for special values `l <= 31` and `l = 41, 47, 59, 73`).

It behaves roughly quadratically for parameter `l`
and roughly linearly in `log q` (the bit size of the base field).

If the base field is a small prime field (characteric less
than 2^64), computations usually take at most a few seconds
even for `l=997`.

Otherwise, it will be much slower due to SageMath implementation
details (as of SageMath 10.0), and possibly take more than 1 minute
for large values of `l`.
