# -*- coding: utf-8 -*-

# for comparing strings

def string_compare(P,S):
    for j in range(len(P)):
        if not P[j] == S[j]:
            return False
    return True


# naive string matcher    
def string_match(T, P):
    n = len(T)
    m = len(P)
    
    positions=[]
    for i in range(n-m+1):
        j = 0
        if string_compare(P,T[i:i+m]):
            positions.append(i)

    return positions
   


def char_to_number(c):
    return ord(c)

# karp_rabin_sum 

def hash_string_sum(P):
    h = 0    
    for j in range(len(P)):
        h += char_to_number(P[j])
    return h
        

def hash_string_sum_update(h, Ti, Tim):
    return h - char_to_number(Ti) + char_to_number(Tim)
    
def karp_rabin_sum(T,P):
    n = len(T)
    m = len(P)
    num_match = 0
    false_hit = 0
    
    
    ht = hash_string_sum(T[0:m])
    h = hash_string_sum(P)
    positions = []
    
    for i in range(n-m+1):
        if ht == h: 
            if string_compare(P,T[i:i+m]):
                num_match += 1
                positions.append(i)
            else:
                false_hit += 1
        
        if i < n-m:
            ht = hash_string_sum_update(ht, T[i], T[i+m])
    return positions, false_hit
            
# karp_rabin_mod

base = 256 
    
def hash_string_mod(P, q):
    h = 0
    # horner
    m = len(P)
    for j in range(m):
        h = (base*h + char_to_number(P[j])) % q
    return h
    
def hash_string_mod_update(h, basem, Ti, Tim, q):
    return (base*(h - basem*char_to_number(Ti)) + char_to_number(Tim))%q
    
def karp_rabin_mod(T,P, q = 1511):
    n = len(T)
    m = len(P)
    #q = 1511 # arbitrary prime number. It should be greater than m

    basem = ((base%q)**(m-1))%q
    num_match = 0
    false_hit = 0
    positions = []
    
    ht = hash_string_mod(T[0:m], q)
    h = hash_string_mod(P, q)
    for i in range(n-m+1):
        if ht == h:
            if string_compare(P,T[i:i+m]):#P == T[i:i+m]:
                num_match += 1
                positions.append(i)
            else:
                false_hit += 1#print("false alarm")
        
        if i < n-m:
            ht = hash_string_mod_update(ht, basem, T[i], T[i+m],q)
    return positions,false_hit

