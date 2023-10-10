# -*- coding: utf-8 -*-
import random

class Graph:
    def __init__(self, L): 
    # vertices are labeled from 0 to n-1  
    # L[i] gives the list of neighbours of vertex i
        self.L=L
        self.n=len(L)

    # draws a random neighbour of vertex i
    def random_neighbour(self,i):
        return self.L[i][random.randint(0,len(self.L[i])-1)]  
        
    # draws a random walk of length k, starting from 0    
    def random_walk(self,k):
        res=[0]
        i=0
        for _ in range(k):
            i=self.random_neighbour(i)
            res.append(i)
        return res
    
    # draws a random walk (starting from 0) till all vertices are visited    
    def random_walk_till_covered(self):
        res=[0]
        i=0
        seen={0:True}
        while(True):
           i=self.random_neighbour(i)
           res.append(i) 
           if not i in seen:
               seen[i]=True
               if len(seen)==self.n:
                   return res
     
    # draws a random spanning tree
    def random_tree(self):
        parent={}
        i=0
        while True:
            j=self.random_neighbour(i)
            if not j==0 and not j in parent:
               parent[j]=i
               if len(parent)==self.n-1:
                   return parent
            i=j          