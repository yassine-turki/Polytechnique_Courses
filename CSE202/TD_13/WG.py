# -*- coding: utf-8 -*-

import random
import math
from UF import *


nr_calls=0

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
        global nr_calls
        nr_calls+=1
        start=L[0]
        end=L[len(L)-1]
        if S==set():
            if start in self.adj[end]:
                newlist=L.copy()+[start]
                return (w+self.adj[start][end],newlist)
            else:
                return (math.inf,[])
        sol=(math.inf,[])
        for vertex in self.adj[end]:
            if vertex in S:
                L.append(vertex)
                S.remove(vertex)
                rec=self.min_cycle_aux(w+self.adj[end][vertex], L, S)
                L.pop()
                S.add(vertex)
                if sol[0]>rec[0]:
                    sol=rec
        return sol
                

    # QUESTION 2
    def vertices(self):
        S=set()
        for x in self.adj:
            S.add(x)
        return S 
    
    def min_cycle(self):
        # TODO
        global nr_calls
        nr_calls=0
        S=self.vertices()
        start=S.pop()
        sol = self.min_cycle_aux(0,[start],S)   
        print("number of calls (min_cycle): ", str(nr_calls))
        return sol
 
    '''
    Question 3
    w_start + w_end + w_S is a lowerbound for the cost of graphs that are from L[0] to a vertex in S, from l[-1] to a vertex in S, 
    and a spanning tree of S. Moreover, in the mincost completion of L into a Hamiltonian circuit,the edges not on the path L form a graph of the previous form. Therefore, our lowerbound is also a lowerbound for the sum of weights of edges 
    not in L, which gives that W>= w_start + w_end + w_S 
    '''   

    # QUESTION 4
    def lower_bound(self,w,L,S): # returns low(L), with w the cost of L, and S the set of vertices not in L
        # TODO
        start=L[0]
        end=L[-1]
        wstart=math.inf
        wend=math.inf
        wS=self.weight_min_tree(S)
        for vertex in self.adj[start]:
            if vertex in S and self.adj[start][vertex]<wstart:
                wstart=self.adj[start][vertex]
        for vertex in self.adj[end]:
            if vertex in S and self.adj[end][vertex]<wend:
                wend=self.adj[end][vertex]
        return w+wstart+wend+wS 
        

    # QUESTION 5
    def min_cycle_aux_using_bound(self,bestsofar,w,L,S):
        # TODO
        global nr_calls  
        nr_calls+=1
        start=L[0] 
        end=L[-1]
        if len(S)==0:
            if start not in self.adj[end] or bestsofar<=w+self.adj[end][start]:
                return (math.inf,[])
            else: 
                newlist=L.copy()+[start]
                return (w+self.adj[end][start],newlist)
        if bestsofar<=self.lower_bound(w,L,S):
            return (math.inf,[])
        sol=(math.inf,[])
        for vertex in self.adj[end]:
            if vertex in S:
                L.append(vertex)
                S.remove(vertex)
                rec=self.min_cycle_aux_using_bound(bestsofar,w+self.adj[end][vertex],L,S)
                L.pop()
                S.add(vertex)
                if sol[0]>rec[0]:
                    sol=rec
                if bestsofar>rec[0]:
                    bestsofar=rec[0]
        return sol 

    def min_cycle_using_bound(self):
        # TODO
        global nr_calls   
        nr_calls=0   
        S=self.vertices()
        vertex=S.pop()
        sol = self.min_cycle_aux_using_bound(math.inf,0,[vertex],S)   
        print("number of calls(min_cycle_aux_using_bound): "+str(nr_calls))  
        return sol   

#################################################################
## Auxiliary methods
#################################################################

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
            print()
