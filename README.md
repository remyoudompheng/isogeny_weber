# Computation of isogenies using Weber modular polynomials

This library implements a computation of isogenies
similar to SageMath `isogenies_prime_degree`
using Weber modular polynomials, following the methods and formulas
found in:

Andrew V. Sutherland, On the evaluation of modular polynomials,
ANTS X, 2013 [arXiv/1202.3985](https://arxiv.org/abs/1202.3985)

It also implements the computation of polynomials itself, and
an application to counting points on elliptic curves as in the above
article.

See also:

Steven Galbraith, Mathematics of public key cryptography, chapter 25
https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html

This script is a hobby project and is not meant to be used
in any serious research or computation.

## Example code

The library only processes elliptic curves defined over finite fields,
with large enough characteristic (`p > 4*l`). Isogenies involving
special curves `j=0` and `j=1728` are not supported.

```python
sage: from isogeny_weber import Database, isogenies_prime_degree_weber

sage: # Without database file
sage: p = next_prime(2**64)
sage: %time list(isogenies_prime_degree_weber(E, 127))
Wall time: 489 ms
[Isogeny of degree 127 from Elliptic Curve defined by y^2 = x^3 + 12*x + 34
over Finite Field of size 18446744073709551629 to Elliptic Curve
defined by y^2 = x^3 + 13924559200224732445*x + 6533477864212809550
over Finite Field of size 18446744073709551629,
 Isogeny of degree 127 from Elliptic Curve defined by y^2 = x^3 + 12*x + 34
 over Finite Field of size 18446744073709551629 to Elliptic Curve
 defined by y^2 = x^3 + 4854534294618478679*x + 16494562990784937922
 over Finite Field of size 18446744073709551629]

sage: # With database file
sage: %time db = Database("weber997.db")
Wall time: 890 ms
sage: p = next_prime(10**24)
sage: E = EllipticCurve(GF(p), [12, 34])
sage: %time list(isogenies_prime_degree_weber(E, 997, weber_db=db))
Wall time: 10.9 s
[Isogeny of degree 997 from Elliptic Curve defined by y^2 = x^3 + 12*x + 34
over Finite Field of size 1000000000000000000000007 to Elliptic Curve
defined by y^2 = x^3 + 511054458339237421057065*x + 872510288008486003302584
over Finite Field of size 1000000000000000000000007,
 Isogeny of degree 997 from Elliptic Curve defined by y^2 = x^3 + 12*x + 34
 over Finite Field of size 1000000000000000000000007 to Elliptic Curve
 defined by y^2 = x^3 + 257209144638154172851337*x + 673351368475851203522052
 over Finite Field of size 1000000000000000000000007]

# Without database file, no isogeny check
sage: p = next_prime(10**12)
sage: K.<i> = GF((p,2), modulus=x^2+1)
sage: E = EllipticCurve(K, [1+2*i, 3+4*i])
sage: %time list(isogenies_prime_degree_weber(E, 997, check=False))
Wall time: 37.3 s
[Isogeny of degree 997 from Elliptic Curve defined by y^2 = x^3 + (2*i+1)*x + (4*i+3)
over Finite Field in i of size 1000000000039^2 to Elliptic Curve defined by
y^2 = x^3 + (327861852685*i+687173276749)*x + (678519152048*i+970771803563)
over Finite Field in i of size 1000000000039^2,
 Isogeny of degree 997 from Elliptic Curve defined by y^2 = x^3 + (2*i+1)*x + (4*i+3)
 over Finite Field in i of size 1000000000039^2 to Elliptic Curve defined by
 y^2 = x^3 + (243554321333*i+281418238038)*x + (992268466242*i+159748093203)
 over Finite Field in i of size 1000000000039^2]
```

## Additional implementation details

Since the Weber modular form is not a rational function of
the j-invariant, it involves working on possibly larger field extensions.
A descent technique is used to reduce equations to the original
base field and speed up computations.

A fast implementation of `adams_operator` is used, following the
ideas of:

Bostan, Flajolet, Salvy, Schost, Fast computation of special resultants
Journal of Symbolic Computation, 41, 1 (2006), 1-29
https://doi.org/10.1016/j.jsc.2005.07.001

The library also uses the sub-quadratic fast Elkies algorithm from article:
which results in faster computation compared to SageMath's implementation
of Stark's algorithm (`compute_isogeny_kernel_polynomial`)

Bostan, Salvy, Morain, Schost, Fast algorithms for computing isogenies between elliptic curves
[arXiv:cs/0609020](https://arxiv.org/pdf/cs/0609020.pdf)

## Database footprint

The Weber modular polynomials are known to use much less
space than classical modular polynomials (about 1728x less space).

An additional symmetry (related to Schläfli modular equation)
is used to eliminate half of these coefficients, and a large
number of trailing zero bits.

An ad-hoc binary encoding is used to store Weber modular
polynomials in a space-efficient way. The resulting files
are 40% the size of original gzipped files available at
https://math.mit.edu/~drew/WeberModPolys.html
and standard compression algorithms will not reduce their size
further. Each polynomial will use about l^3/1000 bytes
(or l^3/900 for large l).

The polynomial database for `l < 512` uses 2.7 MiB of disk or memory,
compared to 27MB for the SageMath `database_kohel` package
(classical modular polynomials for `l <= 113`, bzip2 compressed)
or 18.3 MiB for the PARI seadata database (Atkin modular polynomials
for `l < 500`, gzip compressed).

The source code contains an inlined copy of the database for
`l <= 160` allowing basic usage without generating a database
file.

| Levels | Original file size (GZIP) | Encoded size |
| ------ | ------------------------- | ------------ |
| 5-997 | 91 MiB | 36 MiB |
| 5-1499 | 467 MiB | 185 MiB |
| 1009-2039 | 1439 MiB | 574 MiB |
| only 4999 | 366 MiB | 149 MiB |

Note that the library can work without any database
by performing necessary computations itself (see below).

## Performance

This implementation is usually much faster than the generic
implementation of `isogenies_prime_degree` factoring torsion
polynomials (but slower than the optimized versions
used for special values `l <= 31` and `l = 41, 47, 59, 71`).

It behaves roughly super-linearly for parameter `l`
and roughly linearly in `log q` (the bit size of the base field).

If the base field is a prime field, computations usually take
at most a few seconds even for `l=997`. It may take a couple of minutes
when working over an extension field depending on CPU performance.

## On-the-fly computation of Weber modular polynomials

The module `isogeny_weber.poldb_compute` performs computations
of Weber modular polynomials. It does not use the isogeny volcano
algorithm, but transcendental methods from:

Andreas Enge, Computing modular polynomials in quasi-linear time,
Math. Comp. 78 (2009), 1809-1824
doi:10.1090/S0025-5718-09-02199-1

The fast computation functions from FLINT library are used.
This is usually faster than PARI `polmodular(l, 1)` which uses
isogeny volcanoes to compute Weber modular polynomials.

It takes a few minutes to recompute polynomials for l < 1000
and about an hour to recompute polynomials for l < 2000.
A regular multi-core computer can compute all polynomials for l < 5000
in less than a day using parallelism.

Note that in the case of SEA, the coefficients of Weber modular polynomials
have approximately the same size as the base field, and computation
of modular polynomials takes a small amount of time compared
to determination of their roots.

## Application to point counting

As an application, a toy implementation of the SEA algorithm
for point counting is provided. It can handle prime moduli
up to approximately 1.4L bits if modular polynomial up to level L
are provided.

For example, using a 200 MiB database of modular polynomials
encoded as described above, curves with size up to 2000 bits
can be processed in a few hours on an average home computer.

There is an extra cost compared to standard modular polynomials
because the f-invariant may be in a larger field extension.
The associated extra cost is either O(l) for each prime
(asymptotically negligible) or comparable to SEA running time
(then it may be up to 50% of total time) when the curve has no 2-torsion point.

Modular polynomials are computed on-the-fly if they are not
supplied. The extra cost is a few percent of total running time.
