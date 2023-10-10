# -*- coding: utf-8 -*-

### For comparing strings

def string_compare(P,S):
    for j in range(len(P)):
        if not P[j] == S[j]:
            return False
    return True


### naive string matcher
def string_match(T, P):
    n = len(T)
    m = len(P)
    l=[]
    for i in range(n-m+1):
        if string_compare(P,T[i:i+m])==True:
            l.append(i)
    return l

### number of characters
base = 256

### karp_rabin_sum

def hash_string_sum(S):
    s=0
    for i in range(len(S)):
        s+=ord(S[i])
    return s

def hash_string_sum_update(h, Ti, Tim):
    return h-ord(Ti)+ord(Tim)

def karp_rabin_sum(T,P):
    lp=[]
    sh=0
    n=len(T)
    m=len(P)
    hp=hash_string_sum(P)
    hTm=hash_string_sum(T[:m])
    
    for i in range(n-m+1):
        if hp==hTm:
            if string_compare(P,T[i:i+m]) == True:
                lp.append(i)
            else:
                sh+=1
        if i!=n-m:
            hTm=hash_string_sum_update(hTm, T[i], T[i+m])
        
    return (lp,sh)


### karp_rabin_mod

def hash_string_mod(S, q):
    h = 0
    for j in range(len(S)):
        h = (base*h + ord(S[j])) % q
    return h

def hash_string_mod_update(h,q, Ti, Tim, dm):
    return (base*(h-dm*ord(Ti))+ord(Tim))%q
    

def karp_rabin_mod(T,P, q):
    
    sh = 0
    lp = []
    n = len(T)  
    m = len(P)
    hp = hash_string_mod(P, q)
    hTm = hash_string_mod(T[:m], q)
    dm = ((base)**(m-1))%q
    for i in range(n-m+1):
        if hp == hTm:
            if string_compare(P,T[i:i+m])==True:
                lp.append(i)
            else:
                sh += 1
        if i < n-m:
            hTm = hash_string_mod_update(hTm, q, T[i], T[i+m],dm)
    return (lp,sh)

