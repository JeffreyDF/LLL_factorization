LLL_factorization
=================

Polynomial time factorization of univariate polynomials over the integers using LLL lattice reduction in Sage.

The code ([factorization.py](https://github.com/JeffreyDF/LLL_factorization/blob/master/factorization.py)) is not meant to be fast but to be a well-documented, working implementation of the most basic algorithm for factoring univariate polynomials using LLL latice reduction (multifactor Hensel lifting is also implemented). It follows Modern Computer Algebra from von zur Gathen and Gerhard. Some more information about the algorithm can be found in [documentation.pdf](https://github.com/JeffreyDF/LLL_factorization/blob/master/documentation.pdf).

[factorization.py](https://github.com/JeffreyDF/LLL_factorization/blob/master/factorization.py) is not in a specific Sage format but in a general Python-format. To get it working you simply need to have [Sage](http://www.sagemath.org) and paste the code in a notebook or in the command line. You should also be able to make it as a standalone script by following http://www.sagemath.org/doc/tutorial/programming.html#section-standalone.
