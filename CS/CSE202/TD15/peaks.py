# -*- coding: utf-8 -*-

### Question 1 ###
def peak_naive(L):
    # TO IMPLEMENT:
    if len(L)==1:
        return 0
    if L[0]>=L[1]:
        return 0
    for i in range(1,len(L)-1):
        if L[i]>=L[i-1] and L[i]>=L[i+1]:
            return i
    if L[-1]>=L[-2]:
        return len(L)-1

### Question 2 ###


def peak(L):
    # TO IMPLEMENT
    return peak_aux(L,0,len(L)-1)


def peak_aux(L, p, q):
    # TO IMPLEMENT
    if abs(q-p)>=2:
        l= (p+q)//2
        mid1= L[l-1]
        mid2=L[l]
        if mid1>=mid2:
            if mid1<L[l-2] and l-1!=p:
                return peak_aux(L, p, l)
            else:
                return l-1
        else:
            if mid2<L[l+1] and l!=q-1:
                return peak_aux(L, l, q)
            else:
                return l
    else:
        if max(L[p],L[q])==L[p]:
            return p
        else:
            return q
   

### Question 3 ###


def is_peak(M, i, j):
    # TO IMPLEMENT
    p=M[i][j]
    mini=min(i+1,len(M)-1)
    maxi=max(i-1,0)
    minj=min(j+1,len(M[0])-1)
    maxj=max(j-1,0)
    return p>= M[mini][j] and p>=M[maxi][j] and p>=M[i][minj] and p>= M[i][maxj]

### Question 4 ###


def peak2d_naive(M):
    # TO IMPLEMENT
    for i in range(len(M)):
        for j in range(len(M[0])):
            if is_peak(M,i,j):
                return (i,j)

### Question 5 ###

def setA(c,d):
    A=set()
    if d-c==1:
        A.add(c)
    else:
        l=(c+d)//2
        A.add(c)
        A.add(l-1)
        A.add(l)
        A.add(d-1)
    return A


def pivot(M, p, q, r, s):
    # TO IMPLEMENT
    A0=setA(p, q)
    A1=setA(r,s)
    F=set()
    for i in A0:
        for j in range(r,s):
            F.add((i,j))
    for i in range(p,q):
        for j in A1:
            F.add((i,j))
    Max=0
    for tup in F:
        i=tup[0]
        j=tup[1]
        if Max<M[i][j]:
            Max=M[i][j]
            sol=(i,j)
    return sol
    

### Question 6 ###


def peak2d(M):
    # TO IMPLEMENT
    return peak2d_aux(M, 0, len(M), 0, len(M[0]))


def peak2d_aux(M, p, q, r, s):
    # TO IMPLEMENT
    i,j= pivot(M,p,q,r,s)
    if q-p<=4 or s-r<=4:
        return (i,j)
    else:
        l=(p+q)//2
        m=(r+s)//2
        if (is_peak(M, i, j)):
            return i,j
        if i>=l:
            if j>=m:
                return peak2d_aux(M, l, q, m, s)
                
            else:
                return peak2d_aux(M, l, q, r, m)
        else:
            if j>=m:
                return peak2d_aux(M, p, l, m, s)
            else:
                 return peak2d_aux(M, p, l, r, m)
