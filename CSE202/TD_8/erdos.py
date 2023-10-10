# -*- coding: utf-8 -*-

from uf import Rank_UF
import random
import math
    
def Erdos_Renyi(N):
    uf=Rank_UF(N)
    count=uf.count
    npairs=0
    while uf.get_count()>1:
        p=random.randint(0, N-1)
        while True:
            q=random.randint(0, N-1)
            if p!=q:
                break
        if not uf.is_connected(p, q):
            uf.union(p, q)
        else:
            npairs+=1
            continue
    return npairs
            