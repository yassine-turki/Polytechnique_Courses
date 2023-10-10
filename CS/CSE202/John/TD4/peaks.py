# -*- coding: utf-8 -*-

### Question 1 ###
def peak_naive(L):
    for i in range(len(L)-1):
        if(L[i] >= L[i+1]):
            return i
    return len(L) - 1

### Question 2 ###   
def peak(L):    
    return peak_aux(L, 0, len(L))
    
def peak_aux(L,p,q): 
    if q-1 ==p:
        return p
    else:
        m = (p+q) //2
        if L[m-1] < L[m]:
            if m == q-1 or L[m] >= L[m+1]:
                return m
            else:
                return peak_aux(L, m, q)
        else:
            if p == m-1 or L[m-1] >= L[m-2]:
                return m-1
            else:
                return peak_aux(L,p,m)

### Question 3 ###
def is_peak(M,i,j):
    n1 = len(M)
    n2 = len(M[0])
    if i >0 and M[i][j] < M[i-1][j]:
        return False
    if i< n1 -1 and M[i][j] < M[i+1][j]:
        return False
    if j>0 and M[i][j] < M[i][j-1]:
        return False
    if j < n2 -1 and M[i][j] < M[i][j+1]:
        return False
    return True 
    
### Question 4 ###
def peak2d_naive(M):
    n1 = len(M)
    n2 = len(M[0])
    for i in range(n1):
        for j in range(n2):
            if is_peak(M, i, j):
                return (i,j)
    
### Question 5 ###
def pivot(M,p,q,r,s):    
    if q <= p+4:
        Apq = range(p,q)
    else:
        m = (p+q)//2
        Apq = [p,m-1,m,q-1]
    
    if r <= s+4:
        Ars = range(r,s)
    else:
        m = (r+s)//2
        Ars = [r,m-1,m,r-1]
        
    p_max = (p,r)
    v_max = M[p][r]
    for i in Apq:
        for j in range(r,s):
            if M[i][j] > v_max:
                v_max = M[i][j]
                p_max = (i,j)
    for i in range(p,q):
        for j in Ars:
            if M[i][j] > v_max:
                v_max = M[i][j]
                p_max = (i,j)
    
    return p_max
    
### Question 6 ###
def peak2d(M):
    return peak2d_aux(M, 0, len(M), 0, len(M[0]))
  
def peak2d_aux(M,p,q,r,s):
    (i,j) = pivot(M,p,q,r,s)
    if is_peak(M, i, j):
        return (i,j)
    
    m1 = (p+q)//2
    m2 = (r+s)//2
    if i < m1:
        if j < m2:
            return peak2d_aux(M, p, m1, r, m2)
        else:
            return peak2d_aux(M, p, m1, m2, s)
    else:
        if j > m2:
            return peak2d_aux(M, m1, q, r, m2)
        else:
            return peak2d_aux(M, m1, q, m2, s)  
