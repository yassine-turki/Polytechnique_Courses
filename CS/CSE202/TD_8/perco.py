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
    l = []
    if G[i-1][j]:
        l.append([i-1,j])
    if G[i+1][j]:
        l.append([i+1,j])
    if j > 0 and G[i][j-1]:
        l.append([i,j-1])
    if j < N-1 and G[i][j+1]:
        l.append([i,j+1])
    return l
    


def make_vacant(UF, G, N, i, j):
    G[i][j]=True
    for neighbor in get_vacant_neighbors(G, N, i, j):
        UF.union(pos_to_int(N,i,j), pos_to_int(N, neighbor[0], neighbor[1]))


def ratio_to_percolate(N):
    Gf=[[False for _ in range(N)] for _ in range(N)]
    Gt=[[True for _ in range(N)]]
    G= Gt+Gf+Gt
    uf=Rank_UF((N+2)*N)
    vacant=0
    
    for j in range(N):
        uf.union(pos_to_int(N,0,0), pos_to_int(N,0,j))
        uf.union(pos_to_int(N,N+1,0), pos_to_int(N,N+1,j))
        
    while not uf.is_connected(pos_to_int(N,0,0), pos_to_int(N,N+1,0)):
        i=random.randint(1,N)
        j=random.randint(0,N-1)
        position=G[i][j]
        if not position:
            make_vacant(uf, G, N, i, j)
            vacant+=1
    return vacant/(N**2)

#The estimate of p* is 0.6
        
    
