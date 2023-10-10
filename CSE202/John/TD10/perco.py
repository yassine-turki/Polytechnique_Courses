# -*- coding: utf-8 -*-

from uf import Rank_UF

import random


def draw_grid(grid, N):
    for ii in range(N):
        i = ii+1
        for j in range(N):
            if grid[i][j] == 0:
                print('X', end='')
            else:
                print(' ', end='')
        print()

def pos_to_int(N, i, j):
    return N*i+j


def get_vacant_neighbors(G,N,i,j):
    neighbors = []
    for k in [-1, 1]:
        if G[i + k][j]: 
            neighbors.append([i+k, j])
    
    if j > 0 and G[i][j-1]:
        neighbors.append([i, j-1])
    if j < N-1 and G[i][j+1]:
        neighbors.append([i, j+1])
    return neighbors
    

def make_vacant(UF, G, N, i, j):
    G[i][j] = True 
    for neighbor in get_vacant_neighbors(G, N, i, j):
        UF.union(pos_to_int(N, i, j), pos_to_int(N, neighbor[0], neighbor[1]))

def ratio_to_percolate(N):
    G = [[False for _ in range(N)] for _ in range(N+2)]
    uf = Rank_UF((N+2)*N)
    
    #Setting first and last rows to vacant. 
    for i in range(N):
        G[0][i] = True 
        G[N+1][i] = True; 
    
        #Union of first row and last row respectively 
        if i > 0:
            uf.union(pos_to_int(N, 0, 0),
                     pos_to_int(N, 0, i))
            uf.union(pos_to_int(N, N+1, 0), 
                     pos_to_int(N, N+1, i))
            
        top = pos_to_int(N, 0, 0)
        bottom = pos_to_int(N, N+1, 0)
        
        nbVacantCells = 0
        while (not uf.is_connected(top, bottom)) :
            i = random.randint(1, N)
            j = random.randint(0, N-1)
            
            if not G[i][j]:
                make_vacant(uf, G, N, i, j)
                nbVacantCells +=1
    
    return nbVacantCells / (N*N)
            
        
