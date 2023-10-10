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

    def min_cycle_aux(self,w,L,S):
        global nr_calls
        nr_calls=nr_calls+1
        a=L[0]; b=L[-1]
        if len(S)==0:
            if a not in self.adj[b]:
                return (math.inf,[])
            else:
                Lc=L[:]
                Lc.append(a)
                return (w+self.adj[b][a],Lc)
        res=(math.inf,[])
        for x in self.adj[b]:
            if x in S:
                L.append(x); S.remove(x)
                outx=self.min_cycle_aux(w+self.adj[b][x],L,S)
                L.pop(); S.add(x)
                if outx[0]<res[0]:
                    res=outx
        return res
  
    def min_cycle(self):
        global nr_calls
        nr_calls=0
        S=self.vertex_set()
        a=S.pop()
        res = self.min_cycle_aux(0,[a],S)
        print("number of calls to min_cycle_aux: "+str(nr_calls))
        return res
  
    def vertex_set(self): # returns the set with all vertices of the graph
        S=set()
        for x in self.adj:
            S.add(x)
        return S
   
    def lower_bound(self,w,L,S):
        # returns low(L), with w the cost of L, and S the set of vertices not in L
        a=L[0]
        b=L[-1]
        min_a=math.inf
        min_b=math.inf
        for x in self.adj[a]:
            if x in S and self.adj[a][x]<min_a:
                min_a=self.adj[a][x]
        for x in self.adj[b]:
            if x in S and self.adj[b][x]<min_b:
                min_b=self.adj[b][x]
        return w+min_a+min_b+self.weight_min_tree(S)
  
    def min_cycle_aux_using_bound(self,bestsofar,w,L,S):
        global nr_calls
        nr_calls=nr_calls+1
        a=L[0]; b=L[-1]
        if len(S)==0:
            if a not in self.adj[b] or w+self.adj[b][a]>=bestsofar:
                return (math.inf,[])
            else:
                Lc=L[:]
                Lc.append(a)
                return (w+self.adj[b][a],Lc)
    
        if self.lower_bound(w,L,S)>=bestsofar:
            return (math.inf,[])
    
        res=(math.inf,[])
        for x in self.adj[b]:
            if x in S:
                L.append(x); S.remove(x)
                outx=self.min_cycle_aux_using_bound(bestsofar,w+self.adj[b][x],L,S)
                L.pop(); S.add(x)
                if outx[0]<res[0]:
                    res=outx
                if outx[0]<bestsofar:
                    bestsofar=outx[0]
        return res
   
    def min_cycle_using_bound(self):
        global nr_calls
        nr_calls=0
        S=self.vertex_set()
        a=S.pop()
        res = self.min_cycle_aux_using_bound(math.inf,0,[a],S)
        print("number of calls to min_cycle_aux_using_bound: "+str(nr_calls))
        return res

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



#################################################################
## Approximate algorithms
#################################################################

 ### PROVIDED

    def random_circuit(self):
        # construct a random circuit
        T = [x for x in self.adj]
        random.shuffle(T)
        return T,self.eval_circuit(T)
     
    def eval_circuit(self, T):
        # evaluate a circuit
        w = 0
        for i in range(1,len(self.adj)):
            w += self.adj[T[i-1]][T[i]]
            
        w += self.adj[T[len(self.adj) -1]][T[0]]
        return w
    
     
    def get(self, T, i):
        # returns the location at L[i] (cyclic: Safe if i < 0 or i > len(L))
        return T[i%(len(self.adj))]
     

 ### Greedy construct
     
    def greedy_select_edges(self):
        S = self.adj.keys()
        edge1 = self.edges[0]
        uf = UF(S)
        C = [edge1]
        
        if len(S) == 1:
            return C
        
        uf.union(edge1[0], edge1[1])
        p,q = uf.find(edge1[0]), uf.find(edge1[1])
        l = [key for key in S]
        degrees = {}
        for k in l:
            degrees[k] = 0
        degrees[edge1[0]] += 1
        degrees[edge1[1]] += 1
        
        
        for e in self.edges:
            if len(C) == len(S) - 1 and uf.find(e[0]) == uf.find(e[1]) and degrees[e[0]] <= 1 and degrees[e[1]] <= 1:
                uf.union(e[0], e[1])
                C.append(e)
                return C
            elif e in C:
                continue 
            elif uf.find(e[0]) != uf.find(e[1]) and degrees[e[0]] <=  1 and degrees[e[1]] <=  1:          
                degrees[e[0]] += 1
                degrees[e[1]] += 1
                p,q = uf.find(edge1[0]), uf.find(edge1[1])
                l = [(p,q),(q,p)]
                uf.union(e[0],e[1])
                C.append(e)
        return C


    def build_circuit_from_edges(self, edges):
        res = []
        w = 0
        for edge in edges:
            w += edge[2]
            if edge[0] not in res:
                res += [edge[0]]
            if edge[1] not in res:
                res += [edge[1]]
        return (w, res)
     
        
    def greedy_min(self):
        edges = self.greedy_select_edges()
        return self.build_circuit_from_edges(edges)


 ### 2-opt

    def evaluate_flip(self, T, i, j):
        gain = 0 
        for e in self.edges:
            if T[i] in e:
                if T[i-1] in e:
                    previous_edge_i = e
                    
                if j+1 >= len(T) -1:
                    if T[-1] in e:
                        new_edge_i = e
                if j+1 < len(T) -1:
                    if T[j+1] in e:
                        new_edge_i = e
                        
            if T[j] in e:
                if T[i-1] in e:
                    new_edge_j = e
                if j+1 >= len(T) -1:
                    if T[-1] in e:
                        previous_edge_j = e
                    
                if j+1 < len(T) -1:
                    if T[j+1] in e:
                        previous_edge_j = e
        gain = previous_edge_j[2] + previous_edge_i[2] - (new_edge_i[2] + new_edge_j[2])
        return gain 

 
    def find_best_opt2(self, T):
        g = 0
        flip = (None, None)
        for i in range(len(T)-1):
            for j in range(len(T)-1):
                gain = self.evaluate_flip(T, i, j)
                if gain > g:
                    g = gain 
                    flip = (i,j)
        return (flip, g)
     
    def do_flip(self, T, i, j):
        new_T = T.copy()
        for m in range(abs(i-j)+1):
            new_T[i+m] = T[j-m]
        T = new_T
        return T 
     
    def opt_2(self, w, T):
        (i,j), gain = self.find_best_opt2(T)
        if gain > 0:
            T = self.do_flip(T, i, j)
            w = w - gain
        return w, T
            
        
     
    def neighborhood_search_opt2(self, w, T):
        w0, T0 = self.opt_2(w, T)
        while w0 < w:
            w = w0
            T = T0
            w0, T0 = self.opt_2(w, T)
        return w, T
