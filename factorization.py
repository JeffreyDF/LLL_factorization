"""
	Project Computeralgebra: Jeffrey De Fauw (2013-2014)
	
	Polynomial time factorization of univariate polynomials 
	over the integers using LLL lattice reduction.
"""


def hensel_step(f, g, h, s, t, m):
    """
       Lifts a factorization f=gh (mod m) and Bezout coefficients (s, t) for (g, h) in Z/m, (g, h) 
       being coprime modulo m, to a factorization f=g*h* (mod m^2) and Bezout coefficients (s*,t*).
    
       Input: polynomials f, g, h, s, t in Z[x] and a natural number m such that
              f = gh (mod m) and sg + th = 1 (mod m). We also assume that lc(f)
              is invertible modulo m, h is monic and deg(s) < deg(h) and 
              deg(t) < deg(g).
       
       Output: a list [g*, h*, s*, t*] of polynomials  in Z[x] such that 
               f = g*h* (mod m^2) and s*h* + t*h* = 1 (mod m^2). We also have 
               g* = g (mod m), h* = h (mod m), s* = s (mod m) and 
               t* = t (mod m), with g*, h*, s*, t* also satisfying the 
               inequalities on the degrees.
    """
    
    # Set the appropriate base rings for the polynomials.
    old_ring = Integers(m)  # Z/m    
    g_old, h_old, t_old, s_old = g.change_ring(old_ring), h.change_ring(old_ring),\
                                 t.change_ring(old_ring), s.change_ring(old_ring)
    
    
    # Check if some input conditions are satisfied:
    # f = gh mod m and sg + th = 1 mod m.    
    if not(f.change_ring(old_ring) == g_old*h_old and s_old*g_old + t_old*h_old == 1):
        if not(f.change_ring(old_ring) == g_old*h_old):
            print "Input conditions not satisfied: f = gh (mod m)."
        else:
            print "Input conditions not satisfied: sg + th = 1 (mod m)."
        return None

    # The ring we will lift to: Z/m^2.
    new_ring = Integers(m^2)
    
    # Set them all in the new ring.
    g, h, t, s = g_old.change_ring(new_ring), h_old.change_ring(new_ring),\
                 t_old.change_ring(new_ring), s_old.change_ring(new_ring)
    
    # Lifting the factorization.
    e = (f - g*h)    
    q, r = (s*e).quo_rem(h)  # Division of se by h in Z/m^2.
    g_, h_ = g + t*e + q*g, h + r
    
    # Lifting the Bezout coefficients.
    b = s*g_ + t*h_ - 1
    c, d = (s*b).quo_rem(h_)  # Division of sb by h_ in Z/m^2.
    s_, t_ = s - d, t - t*b - c*g_
    
    # Return the polynomials as embedded in Z[x].
    return [g_.change_ring(ZZ), h_.change_ring(ZZ), 
            s_.change_ring(ZZ), t_.change_ring(ZZ)]
            
            
def list_product(some_list):
    """
        Returns the product of all the elements in the input list.    
    """
    product = 1
    
    for element in some_list:
        product *= element
        
    return product
  
    
def multi_hensel(f, p, l):
    """
       This is the multifactor extension of hensel_step, albeit for a lifting of a factorization
       over Z/p to a factorization over Z/p^l. It factorizes the polynomial f over Z/p, recursively 
       splits the factors and then eventually returns by lifting each pair of factors (g, h) modulo p 
       to factors (g*, h*) modulo p^l with hensel_step().
    
       Input: a polynomial f in Z[x], a prime p, s.t. lc(f) nonzero modulo p, and a natural number l.
       
       Output: a list [b, f*_1, ..., f*_r] of polynomials f*_1, ..., f*_r in Z[x] and an
               integer b such that f = b f*_1 ... f*_r (mod p^l) and f*_i = f_i (mod p),
               where f = b f_1 ... f_r (mod p), pairwise corpime modulo p.
    """
    
    # Setting up the variables: the base ring and the ring to lift to.
    old_ring = Integers(p)  # Z/p.
    new_ring = Integers(p^l)  # Z/p^l.
    
    # Do initial factoring in Z/p.
    F = f.factor_mod(p)
    # Add the lc and factors to list f_i.
    f_i = []    
    f_i.append(F.unit())    
    for [factor, e] in F:
		if e > 1:
			print "f mod p not square-free."
			break
		f_i.append(factor.change_ring(ZZ))
    
    lc_f = int(f_i[0])  # The leading coefficient.
    r = len(f_i)-1  # Number of factors.
    
    # If only one factor, return.
    if r == 1:
        # Determine f^\star_1 s.t. f = lc(f)f^\star_1 mod p^l.
        f_ = (f.change_ring(new_ring) / lc_f).change_ring(ZZ)
        return [lc_f, f_]
    
    # The index k at which to split the factors and the number of
    # consecutive lifts d.
    k, d = int(r/2), int(log(l, 2)) + 1
    
    # Factor f in f = g_ h_ with:
	# g_ = lc(f)f_1 * ... * f_k mod p and h_ = f_{k+1} * ... * f_r mod p.
    g_ = (lc_f * list_product(f_i[1:k+1])).change_ring(ZZ)
    h_ = (list_product(f_i[k+1:])).change_ring(ZZ)
    
    # Determine the Bezout coefficients.
    d_, s_, t_ = xgcd(g_.change_ring(old_ring), h_.change_ring(old_ring))
    if d_ != 1:
        print "Not Bezout-coprime!"
    else:
        s_ = s_.change_ring(ZZ)
        t_ = t_.change_ring(ZZ)
        
    # Do d consecutive Hensel steps.
    for j in xrange(1, d+1):
		m = p^(2^(j-1))
		g_, h_, s_, t_ = hensel_step(f, g_, h_, s_, t_, m)
        
    # Recursive on the first factor g_.
    g_factors = multi_hensel(g_, p, l)
    
    # Recursive on the second factor h_.
    h_factors = multi_hensel(h_, p, l)
       
    return g_factors + h_factors[1:]
 
    
def lll_reduc(f_i):
    """
       Returns the LLL-reduced (almost orthogonal) basis for the lattice L with basis vectors the 
       vectors in the input list. The reduced basis (g_i)_i satisfies ||g_i||^2 <= 2 ||g_{i+1}||^2, 
       for 1 <= 1 < dim(L).
    
       Input: list of n basis vectors (f_i)_i for a lattice Z^n.
       
       Output: a list containing the reduced basis vectors (g_i)_i (in order).
    """
    
    # Construct matrix with the input rows.
    A = Matrix(ZZ, f_i)

    # Check some input conditions.
    if A.is_square() is False or A.base_ring() is not ZZ or A.det() is 0:
        print "Check that the input is a non-singular, square matrix over ZZ."

    n = A.dimensions()[0]

    # Initialize G=(g_i)_i.
    G = A.change_ring(QQ)   
    G_, M = G.gram_schmidt()

    i = 1
    while i < n:
        # Replace the basis vectors for the lattice with an integer approximation 
        # of the orthogonal basis. (This is a lazy implementation since it is overkill 
        # to call gram_schmidt again.)
        for k in range(i):
            j = (i-1) - k
            
            new_row = G.row(i) - int(M[i, j]+1/2)*G.row(j)
            G.set_row(i, new_row)
            # Update the GSO.
            G_, M = G.gram_schmidt()
        
        # If it does not satisfy the reduced basis condition, swap rows with the previous vector.
        if i > 0 and G_.row(i-1).norm()^2 > 2*G_.row(i).norm()^2:
            # Swap rows.
            tmp = G.row(i)
            G.set_row(i, G.row(i-1))
            G.set_row(i-1, tmp)

            # Update the GSO.
            G_, M = G.gram_schmidt()
            # Return one step.
            i -= 1
        else:
            # Next vector.
            i += 1

    # Return reduced basis vectors in list.        
    return [row for row in G.rows()]


def coefs_repr(coefs, m):
    """
       Some helper method for the LLL-factorization. Input is a list of integers which are then 
       "mapped" to the symmetric representation of Z/m given by {-(m-1)/2, ..., 0, ..., (m-1)/2} 
       with the obvious group laws.
    """
    return [coef if coef <= (m-1)/2 else coef - m for coef in coefs]


def poly_repr(f, m):
    """
       Some helper method for the LLL-factorization. Input is a polynomial in Z[x] which is 
       transformed to a polynomial in Z/m[x] but with the symmetric representation for Z/m as 
       {-(m-1)/2, ..., 0, ..., (m-1)/2}, as returned by coefs_repr.
    """    
    coefs = coefs_repr(f.coeffs(), m)    
    f_ = 0
    for i in xrange(len(coefs)):
        f_ += coefs[i]*x^i
    
    return f_
    

def factor_lll(f):
    """
       Returns the factorization in irreducible factors of a square-free primitive polynomial f, 
       with nonzero leading coefficient, in Z[x].
    
       Input: a polynomial f in Z[x].
       
       Output: a list with the irreducible, monic factors of f in Z[x].
    """
    # Check if square-free.
    #if not f.is_squarefree():
        #print "f not square-free."
        #return None
    
    # Convert polynomial into coefficient vector.
    f_v = vector(ZZ, f.coeffs())    
    
    A = f_v.norm(Infinity)  # The max norm of the coeffients of f.

    n = f_v.degree() - 1
    if n == 1:
        # No factoring to be done.
        return f

    # Define some constants.
    b = f_v[n]  # The leading coefficient.
    B = sqrt(n+1)*2^n*A*b
    C = (n+1)^(2*n)*A^(2*n-1)
    gamma = int(2*log(C,2))+1
        
    # Search for a prime p and power l s.t. the f mod p is square-free
    # and lc(f) mod p is nonzero.
    search = True
    while search:
        # Random prime between 3 and ceil(2\gamma ln(\gamma)).
        p = random_prime(int(2*gamma*ln(gamma)), 3)        
        f_ = f.change_ring(Integers(p))
        f_x = f_.derivative()
        
        # Stop searching when conditions are satisfied.
        if xgcd(f_, f_x)[0] == 1 and b % p != 0:
            search = False
         
    l = int(log(2^(n^2/2)*B^(2*n), p)) + 1  # The prime power.
    print "Prime %i and exponent %i.\n" % (p, l)

    
    F = f.factor_mod(p)  # Do initial factoring of f over Z/p.
    # Add the lc and factors to list h_i.
    h_i = []
    h_i.append(b)
    for [factor, e] in F:
        # Check if single factor, else print warning and stop.
        if e > 1:
            print "Not square-free."
            return None
        # Append the factor with the symmetric represention of Z/p.
        h_i.append(poly_repr(factor.change_ring(ZZ), p))

        
    # Hensel lift the factors to Z/p^l.
    g_i = []
    g_i.append(b)
    for factor in multi_hensel(f, p, l)[1:]:
        # Append the factor with the symmetric represention of Z/p^l.
        g_i.append(poly_repr(factor, p^l))

    
    r = len(g_i)-1  # Number of modular factors.    
    T = [i+1 for i in xrange(r)]  # The list of modular factors left.    
    G = []  # Factors in Z[x] found.  
    f_ = f  # Left to factor.

    old_ring = Integers(p)
    new_ring = Integers(p^l)
    while len(T) != 0:
        # Choose u of max degree among the modular factors.
        u = sorted([fact for fact in g_i if g_i.index(fact) in T], 
                   key=lambda r: -(r.degree()))[0]

        u_ =  (b*u).change_ring(new_ring)  # Find u_ = bu mod p^l.         
        u_ = poly_repr(u_.change_ring(ZZ), p^l)  # Symmetric representation Z/p^l.
  
        # Check if u is already a true factor of f.
        q, r = (b*f_).change_ring(ZZ).quo_rem(u_)         
        if r == 0:
            print "u=%s is already a factor!" % u_
            
            # Update the search variables.
            g_ = u_  # Set the true factor u_ as g_ (same notation as in search in lattice).            
            S = [jj for jj in T if g_.change_ring(old_ring).quo_rem(h_i[jj])[1] == 0]
            
            # If this is the only factor left, add the factor and break.
            if len([jj for jj in T if jj not in S]) == 0:
                #print "T AND S", T, S
                G.append(g_/g_.content())
                break
            
            # Still left to factor.  
            h_ = (b*list_product([g_i[jj].change_ring(new_ring) 
                                  for jj in T if jj not in S])).change_ring(ZZ)
            h_ = poly_repr(h_, p^l) 
            f_ = h_/h_.content()
            
            T = [jj for jj in T if jj not in S]  # Remove the indices in S from T.
            G.append(g_/g_.content())  # The found factor.
            b = int(f_.coeffs()[-1])  # The lc.        
        
        # u is not a true factor, find the irreducible factor of f_ divisible by u mod p^l.
        else:        
            d, n_ = u.degree(), f_.degree()
            
            # Compute short vector in lattice of dimension j, representing a polynomial
            # of degree less than l divisible by u modulo p^l. 
            b_break = False  # Boolean used to check if we used break below.
            
            for j in xrange(d+1, n_+1):
                # The j generators for the lattice.
                L_gens_ = [(u*x^jj).coeffs() for jj in xrange(j-d)]
                L_gens_ += [(p^l*x^jj).coeffs() for jj in xrange(d)]
                
                # Extend vectors with zeros to the right dimension.
                L_gens = [vector(ZZ, gen + [0 for jj in xrange(j-len(gen))]) for gen in L_gens_]
                
                # Get short vector from LLL-reduced basis and use the symmetric representation
                # of Z/p^l for the coefficients (embedded in Z).
                g_v = vector(ZZ, coefs_repr(lll_reduc(L_gens)[0], p^l))
                
                # The corresponding (short) polynomial g_.
                g_ = 0        
                for jj in xrange(j):
                    g_ += g_v[jj]*x^jj
                g_ = poly_repr(g_, p^l)  # Symmetric representation Z/p^l.
                    
                # Set S of indices representing the modular factors h_i of g_. 
                S = [jj for jj in T if g_.change_ring(old_ring).quo_rem(h_i[jj])[1] == 0]
                
                # The remaining polynomial modulo p^l as product of the corresponding g_i.
                h_ = (b*list_product([g_i[jj].change_ring(new_ring) 
                                      for jj in T if jj not in S])).change_ring(ZZ)
                h_ = poly_repr(h_, p^l)  # Symmetric representation Z/p^l.            
                h_v = vector(ZZ, coefs_repr(h_.coeffs(), p^l))  # Corresponding coefficient vector for h_.
                
                # Extend the vectors again.
                d_max = max(len(h_v), len(g_v))  # Max dimension of the two vectors.
                g_v = vector(ZZ, list(g_v) + [0 for jj in xrange(d_max - len(g_v))]) / g_.content()
                h_v = vector(ZZ, list(h_v) + [0 for jj in xrange(d_max - len(h_v))]) / h_.content()
                
                # Mignotte's bound.
                if g_v.norm(1) * h_v.norm(1) <= B:
                    # Can lift the factorization to Z[x].
                    #print "Lattice reduction."     
                    
                    # Add the irreducible factor of f_.
                    G.append(g_/g_.content())                  
                    # Update the search variables.
                    T = [jj for jj in T if jj not in S]
                    f_ = h_/h_.content()
                    b = int(f_.coeffs()[-1])
                    b_break = True
                    break
            
            # Check if we break-ed out of the loop.
            if not b_break:
                # If not, end search.
                T = []
                G.append(f_)
            else:
                b_break = False
        
    return G
    
    
R.<x> = PolynomialRing(ZZ)
%timeit
factor_lll((x+11)*(x-222)*(x-3333)*(x^2+x+1)*(x+67))

%prun 
factor_lll((x-222)*(x-3333)*(x^2+x+1))
