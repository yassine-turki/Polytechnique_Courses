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
        n=len(self.L[i])-1
        integer= random.randint(0,n)
        return self.L[i][integer]
        
    # draws a random walk of length k, starting from 0    
    def random_walk(self,k):
        l=[0 for _ in range(k+1)]
        for i in range(1,k+1):
            element=self.random_neighbour(l[i-1])
            l[i]=element
        return l
            
    
    # draws a random walk (starting from 0) till all vertices are visited    
    def random_walk_till_covered(self):
        s={0}
        walk=[0]
        while self.n!=len(s):
            element=self.random_neighbour(walk[-1])
            walk.append(element)
            if element not in s:
                s.add(element)
        return walk
                
     
    # draws a random spanning tree
    def random_tree(self):
        s={0}
        walk=[0]
        d={x:0 for x in range(1,self.n)}
        while self.n!=len(s):
            element=self.random_neighbour(walk[-1])
            if element not in s:
                d[element]=walk[-1]
                s.add(element)
                
            walk.append(element)
        return d
                
        