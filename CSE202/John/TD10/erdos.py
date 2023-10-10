# -*- coding: utf-8 -*-

from uf import Rank_UF
import random
import math
    
def Erdos_Renyi(N):
    uf = Rank_UF(N)
    numberofpairs = 0
    while uf.count > 1:
        p = random.randint(0, N-1)
        q = random.randint(0, N-1)
        while p == q:
            q = random.randint(0, N-1)
        numberofpairs +=1 
        
        if uf.is_connected(p,q):
            continue
        else:
            uf.union(p,q)
    
    return numberofpairs
            