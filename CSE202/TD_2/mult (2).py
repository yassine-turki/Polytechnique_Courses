# -*- coding: utf-8 -*-

# Q1

def poly_mult(P,Q):
    product = [0 for _ in range(len(P) + len(Q) -1 )]
    for i in range(len(P)):
        for j in range(len(Q)):
            if (i+j < len(P) + len(Q) - 1):
                product[i+j] += P[i] * Q[j]
    return product

def cost_mult(n): 
    return (2*n*n -n - n +1)
    
# Q2

def poly_add(P,Q):
    size1 = len(P)
    size2 = len(Q)
    if size1 > size2:
        s = P
        for i in range(size2):
            s[i] += Q[i]
    else:
        s = Q
        for i in range(size1):
            s[i] += P[i]
    return s
         
def neg(P):
    Q = [0 for _ in range(len(P))]
    for i  in range(len(P)):
        Q[i] = -P[i]
    return Q
   
def shift(P,k):
    size = len(P) +k 
    result = [0 for _ in range(size)]
    for i in range(len(P)):
        result[i+k] = P[i]
    return result 
  
# Q3  
  
def poly_kara_mult(P,Q):
    n = len(P)
    if n == 1:
        return [P[0] * Q[0]]
    k = (n+1)//2 
    P0 = [P[i] for i in range(k)]
    P1 = [P[i] for i in range(k, n)]
    Q0 = [Q[i] for i in range(k)]
    Q1 = [Q[i] for i in range(k, n)]
    H0 = poly_kara_mult(P0, Q0)
    H2 = poly_kara_mult(P1, Q1)
    H1 = poly_kara_mult(poly_add(P0,P1), poly_add(Q0, Q1))
    
    return poly_add(H0, 
                    poly_add(
                        shift(poly_add(
                            poly_add(H1, neg(H0)), neg(H2)), k),shift(H2, 2*k)))

    
    
        
        
    
def cost_poly_kara_mult(n):
    if n ==1 : return 1
    return 3 * cost_poly_kara_mult((n+1)//2) + 4*n


# Q4 

def cost_poly_tc3_mult(n):
    if n == 1: 
        return 1
    elif n == 2: 
        return 3
    else: 
        return 5 * cost_poly_tc3_mult((n+2)//3) + 30 *n
    pass

# Q5 hybrid
   
def poly_switch_mult(d,P,Q):
    n = len(P)
    if n <= d:
        return poly_mult(P, Q)
    else:
        k = (n+1)//2 
        P0 = [P[i] for i in range(k)]
        P1 = [P[i] for i in range(k, n)]
        Q0 = [Q[i] for i in range(k)]
        Q1 = [Q[i] for i in range(k, n)]
        H0 = poly_switch_mult(d,P0, Q0)
        H2 = poly_switch_mult(d,P1, Q1)
        H1 = poly_switch_mult(d,poly_add(P0,P1), poly_add(Q0, Q1))
    
    return poly_add(H0, 
                    poly_add(
                        shift(poly_add(
                            poly_add(H1, neg(H0)), neg(H2)), k),shift(H2, 2*k)))

        

def cost_switch_mult(d,n):
    if n <= d: 
        return 2*n**2 - 2*n +1 
    else:
        return 3* cost_switch_mult(d, (n+1)//2) + 4*n

   
