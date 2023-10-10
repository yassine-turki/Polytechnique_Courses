# -*- coding: utf-8 -*-

import random
import math
from UF import *

class WG:
    def __init__(self, L): # L is the list of edges
        L.sort(key= lambda e: e[2])
        self.edges=L
        self.adj={}
        for x in L:
            if x[0] not in self.adj:
                self.adj[x[0]]={x[1]:x[2]}
            else:
                self.adj[x[0]][x[1]]=x[2]
            if x[1] not in self.adj:
                self.adj[x[1]]={x[0]:x[2]}
            else:
                self.adj[x[1]][x[0]]=x[2]

    # QUESTION 1	
    def min_cycle_aux(self,w,L,S): 
        #First we get the extremas of the path. 
        a = L[0]
        b = L[-1]
        if len(S) == 0:
            if a not in self.adj[b]:
                return (math.inf, [])
            else:
                #Case where a and b are adjoint
                vertices = L[:]
                vertices.append(a)
                return (w + self.adj[b][a], vertices)
        else:
            res = (math.inf, [])
            for adj in self.adj[b]:
                if adj in S: 
                    L.append(adj)
                    S.remove(adj)
                    tmp = self.min_cycle_aux(w + self.adj[b][adj], L, S)
                    L.pop()
                    S.add(adj)
                    if tmp[0] < res[0]:
                        res = tmp
            return res

  
    # QUESTION 2
    def min_cycle(self):
        S = self.vertex()
        start = S.pop()
        res = self.min_cycle_aux(0, [start], S)
        return res

"""
The miniaml cost over subgraphs that are made of an edge from v1 to S, an edge from vk to S, 
 and a spanning tree of S is given by w_{start}+w_{end}+w_S. 
 When we compute the mincost completion of L into a Hamiltonian circuit, 
 the set of edges not on the path L returns a similar subgraph. 
 This gives W >= w_{start}+w_{end}+w_S    
"""


 Note that, in the mincost completion 
 of L into a Hamiltonian circuit, the set of edges not on the path L 
 gives a subgraph of that form, hence the total weight of edges 
 not on L is at least w_{start}+w_{end}+w_S   


    
    
    # QUESTION 4
    def lower_bound(self,w,L,S): # returns low(L), with w the cost of L, and S the set of vertices not in L
        a = L[0]
        b = L[-1]
        min_a = math.inf
        min_b = math.inf
        for adj in self.adj[a]:
            if adj in S and self.adj[a][adj] < min_a:
                min_a = self.adj[a][adj]
        for adj in self.adj[b]:
            if adj in S and self.adj[b][adj] < min_b:
                min_b = self.adj[b][adj]
        return w + min_a + min_b + self.weight_min_tree(S)
  
    # QUESTION 5
    def min_cycle_aux_using_bound(self,bestsofar,w,L,S): 
        # TO COMPLETE
        a = L[0]
        b = L[-1]
        if len(S) == 0:
            if a not in self.adj[b] or w + self.adj[b][a] > bestsofar:
                return (math.inf, [])
            else:
                #Case where a and b are adjoint
                vertices = L[:]
                vertices.append(a)
                return (w + self.adj[b][a], vertices)
            
        elif self.lower_bound(w, L, S) > bestsofar:
            return (math.inf, [])
            
        else:
            res = (math.inf, [])
            for adj in self.adj[b]:
                if adj in S: 
                    L.append(adj)
                    S.remove(adj)
                    tmp = self.min_cycle_aux_using_bound(bestsofar, w + self.adj[b][adj], L, S)
                    L.pop()
                    S.add(adj)
                    if tmp[0] < res[0]:
                        res = tmp
                    if tmp[0] < bestsofar:
                        bestsofar = tmp[0]
            return res
    
    
    
    
    def min_cycle_using_bound(self): 
        S = self.vertex()
        a = S.pop()
        res = self.min_cycle_aux_using_bound(math.inf, 0, [a], S)
        return res
  
#################################################################
## Auxiliary methods
#################################################################

    #AUX METHOD FOR QUESTION 2
    def vertex(self):
        S = set()
        for v in self.adj:
            S.add(v)
        return S

    

    def weight_min_tree(self,S): # mincost among all trees whose spanned vertices are those in S
        if len(S)==1: return 0
        if len(S)==2:
            L=list(S)
            if L[0] in self.adj[L[1]]: return self.adj[L[0]][L[1]]
            else: return math.inf    
        uf=UF(S)
        nr_components=len(S) 
        weight=0
        for e in self.edges:
            if e[0] in S and e[1] in S:
                if uf.find(e[0])!=uf.find(e[1]):
                    weight=weight+e[2]
                    uf.union(e[0],e[1]) 
                    nr_components=nr_components-1
                    if nr_components==1:
                        return weight        
        return math.inf
     
    def induce_by_subset(self,S): # reduces self.adj to keep only the edges with both ends in S 
        new_adj={}
        for x in self.adj:
            for y in self.adj[x]:
                if x in S and y in S:
                    if x not in new_adj:
                        new_adj[x]={y:self.adj[x][y]}
                    else:
                        new_adj[x][y]=self.adj[x][y]
                    if y not in new_adj:
                        new_adj[y]={x:self.adj[y][x]}
                    else:
                        new_adj[y][x]=self.adj[y][x]    
        self.adj=new_adj          

    def display(self):
        print("Graph has "+str(len(self.adj))+" vertices")
        print()   
        for x,y in self.adj.items():
            print("Neighbours of "+str(x)+":")	
            for t,u in y.items(): 
                print(str(t)+" with weight "+str(u))
            print()      # -*- coding: utf-8 -*-

