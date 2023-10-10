# -*- coding: utf-8 -*-

import random

def random_element(dict):
    s = 0
    d = {}
    for v in dict.values():
        s +=v
    i = random.random()
    for x,y in dict.items():
        d[x] = y/s
    #i = random.random()
        if i < d[x]:
            return x
        else:
            i = i-d[x] 
    
class MultiGraph:
    
    def __init__(self, L):
        
        self.adj={}
        self.deg={}
        for x in L[1]:
            if x[0] not in self.adj:
                self.adj[x[0]]={x[1]:x[2]}
                self.deg[x[0]]=x[2]
            else:
                self.adj[x[0]][x[1]]=x[2]
                self.deg[x[0]]+=x[2]
            if x[1] not in self.adj:
                self.adj[x[1]]={x[0]:x[2]}
                self.deg[x[1]]=x[2]
            else:
                self.adj[x[1]][x[0]]=x[2]
                self.deg[x[1]]+=x[2]
                
    def subset_from_integer(self,i):# i is an integer between 1 and 2^n-2, with n the number of vertices
        subset={}
        for x in self.adj:
            if i%2==1:
                subset[x]=True
                i=i>>1
        return subset
        
    def cutsize(self,i):# i is an integer between 1 and 2^n-2, with n the number of vertices
        c = 0
        S1={}
        for x in self.adj:
            if i%2==1:
              S1[x]=True
            i=i>>1
        for x,y in self.adj.items():
            for t,u in y.items():
                if x in S1 and not t in S1:
                    c+=u
        return [c,[x for x in S1]]
             
 
 
 
 
 
  # TO COMPLETE


    def random_vertex(self):
        res = random_element(self.deg)
        return res
    
    def random_edge(self):
        i = self.random_vertex()
        j = random_element(self.adj[i])
        return (i,j)
      
       
    def contract(self,i,j):# contracts edge i,j (i absorbs j)
      edge = self.adj[i][j]
      del self.adj[i][j]
      del self.adj[j][i]
      self.deg[i] -= edge
      for x, y in self.adj[j].items():
          if x in self.adj[i]:
              self.adj[i][x] += y
              self.adj[x][i] += y
            
          else:
              self.adj[i][x] = y
              self.adj[x][i] = y
          del self.adj[x][j]
          self.deg[i] +=y
      del self.adj[j]
      del self.deg[j]
            
          
     
    
    def display(self):
      for x,y in self.adj.items():
         print("Neighbours of "+str(x)+", which has degree "+str(self.deg[x]))	
         for t,u in y.items(): 
            print(str(t)+" with multiplicity "+str(u))
    
       
