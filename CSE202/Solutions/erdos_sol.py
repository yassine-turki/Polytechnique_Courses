# -*- coding: utf-8 -*-

from uf import Rank_UF
import random
import matplotlib.pyplot as plt
import math 
 
 
def test_erdos():
    x = range(10, 1000, 10)
    y = []
    for i in x:
        y.append(Erdos_Renyi(i))
        
    plt.plot(x,y, color='red', label='experimental')
    plt.plot(x,[(math.log(N))*(N-1)/2 for N in x], color='blue', label='model')
    
    plt.legend(loc='upper left')
    
    plt.xlabel('N')
    plt.ylabel('#Edges')
    plt.title('Erdos-Renyi: number of edges for being connected')
    plt.show()
    
def Erdos_Renyi(N):
    '''
        TO IMPLEMENT
    '''
    uf = Rank_UF(N)
    count_it = 0
    while uf.count > 1:
        p = random.randint(0,N-1)
        q=random.randint(0,N-1)
        while q == p:
            q = random.randint(0,N-1)
        
        count_it += 1
        
        if uf.is_connected(p,q):
            continue
        
        
        
        uf.union(p,q)
        
    return count_it
    
test_erdos()