# -*- coding: utf-8 -*-

from uf import Rank_UF

import random
import matplotlib.pyplot as plt



def draw_grid(grid, N):
    for ii in range(N):
        i = ii+1
        for j in range(N):
            if not grid[i][j]:
                print('X', end='')
            else:
                print(' ', end='')
        print()

def pos_to_int(N, i, j):
    return N*i+j


def get_vacant_neighbors(G,N,i,j):
    '''
        TO IMPLEMENT
    '''
    L = []
    for k in [-1, 1]:
        if G[i+k][j]:
            L.append([i+k,j])

    if j > 0 and G[i][j-1]:
        L.append([i, j-1])
    if j < N-1 and G[i][j+1]:
        L.append([i, j+1])
    return L

def make_vacant(UF, G, N, i, j):
    '''
        TO IMPLEMENT
    '''
    G[i][j] = True
    for pos in get_vacant_neighbors(G,N,i,j):
        UF.union(pos_to_int(N,i,j), pos_to_int(N,pos[0],pos[1]))
     

def ratio_to_percolate(N):
    '''
        TO IMPLEMENT
    '''
    rows = N+2
    grid = [[False for j in range(N)] for i in range(N+2)]
    uf = Rank_UF(rows*N)
    
    for i in range(N):
        grid[0][i] = True
        grid[N+1][i] = True
        if i > 0:            
            uf.union(pos_to_int(N,0,0), pos_to_int(N,0,i))
            uf.union(pos_to_int(N,N+1,0), pos_to_int(N,N+1,i))
    
    top = pos_to_int(N,0,0)
    bottom = pos_to_int(N,N+1,0)
    
    count = 0
    while not uf.is_connected(top, bottom):
        
#        r = random.randint(N, (N+1)*N -1)
#        (i,j) = int_to_pos(N,r)
        
        i = random.randint(1,N)
        j = random.randint(0,N-1)
        
        if not grid[i][j]:
            make_vacant(uf, grid,N,i,j)
            count += 1

    #draw_grid(grid, N)            
    return count / (N*N)


N = 20
print(N, ratio_to_percolate(N))    
N = 50
print(N, ratio_to_percolate(N))
N = 100
print(N, ratio_to_percolate(N))
N = 100
print(N, ratio_to_percolate(N))
       
### (NOT ASKED) Plot proba of vacant vs proba of percolation
def percolate(p, N):
    rows = N+2
    grid = [[(True if random.random() < p else False)  for j in range(N)] for i in range(N+2)]   
    
    
    uf = Rank_UF(rows*N)    
    #draw_grid(grid, N) 
    
    for i in range(N):
        grid[0][i] = 1
        grid[N+1][i] = 1
        if i > 0:            
            uf.union(pos_to_int(N,0,0), pos_to_int(N,0,i))
            uf.union(pos_to_int(N,N+1,0), pos_to_int(N,N+1,i))
    
       

    for ii in range(N):
        i = ii+1
        for j in range(N):
            if grid[i][j] == 0:
                continue
            
            L = get_vacant_neighbors(grid, N, i,j)
            for pos in L:
                uf.union(pos_to_int(N,i,j), pos_to_int(N,pos[0],pos[1]))
    
    if uf.is_connected(pos_to_int(N,0,0), pos_to_int(N,N+1,0)):
        return True
    else:
        return False
  

def check_percolate(N):
    x = [0+th*2/100 for th in range(1,50)]
    y = []    
    T = 100
    
    for p in x:
        count = 0
        for _ in range(T):
            if percolate(p, N):
                count += 1
        y.append(count/T)
        
    plt.plot(x,y)
    
    plt.title('P(vacant) vs proba of percolating (N='+str(N)+')')
    plt.show()
        

print(percolate(0.2, 25))
check_percolate(10)
