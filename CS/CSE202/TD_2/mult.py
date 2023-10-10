# -*- coding: utf-8 -*-

# Q1
import math
def poly_mult(P,Q):
    l=[]
    for _ in range(len(P)+len(Q)-1):
        l.append(0)
    for n in range(len(P)):
        for i in range(len(Q)):
            l[n+i]+=P[n]*Q[i]
    return l
            

def cost_poly_mult(n): 
    return 2*n**2 - n - n + 1

# Q2

def poly_add(P,Q):
    if len(P)>len(Q):
        x=P
        y=Q
    else:
        x=Q
        y=P
    for i in range(len(y)):
        x[i]+=y[i]
    return x
        
         
def neg(P):
    return [-P[i] for i in range(len(P))]

def shift(P,k):
    Q=[P[i] for i in range(len(P))]
    for i in range(k):
        Q.insert(i,0)
    return Q
  
# Q3  
  
def poly_kara_mult(P,Q):
    n=len(P)
    if n<=10:
        return poly_mult(P, Q)
    k=math.ceil(n/2)
    P0=P[0]
    P1=P[1]
    P_split=P0+shift(P,k)
    Q0=Q[0]
    Q1=Q[1]
    Q_split=Q0+shift(Q,k)
    H0=poly_kara_mult(P1,Q1)
    H2=poly_kara_mult(P1,Q1)
    H1_wave=poly_kara_mult(poly_add(P0,P1),poly_add(Q0,Q1))
    return H0+shift(H1_wave-H0-H2,k)+shift(H2,2*k)

def cost_poly_kara_mult(n):
    l=[0]*n
    if n==1:
        return 1
    return 3*cost_poly_kara_mult(math.ceil(n/2)) + 4*n
    
# Q4 

def cost_poly_tc3_mult(n):
    if n==1:
        return 1
    if n==2:
        return 3
    return 5*cost_poly_tc3_mult(math.ceil(n/3))+30*n

# Q5 hybrid
   
def poly_switch_mult(d,P,Q):
    n = len(P)
    if n <= d:
        return poly_mult(P, Q)
    else:
        k = math.ceil(n/2)
        P0 = [P[i] for i in range(k)]
        P1 = [P[i] for i in range(k, n)]
        Q0 = [Q[i] for i in range(k)]
        Q1 = [Q[i] for i in range(k, n)]
        H0 = poly_switch_mult(d,P0, Q0)
        H2 = poly_switch_mult(d,P1, Q1)
        newP=poly_add(P0,P1)
        newQ=poly_add(Q0, Q1)
        H1_hat = poly_switch_mult(d,newP,newQ)
        pol0=shift(poly_add(poly_add(H1_hat,neg(H0)), neg(H2)), k)
        pol1=poly_add(pol0,shift(H2, 2*k))
    
    return poly_add(H0,pol1)
    

def cost_switch_mult(d,n):
    if n<=d:
        return 2*n**2-2*n+1
    return 3*cost_switch_mult(d,math.ceil(n/2))+4*n

   
