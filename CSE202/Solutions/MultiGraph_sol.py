# -*- coding: utf-8 -*-

import random

def random_element(dict):
   N=0
   for x in dict:
     N+=dict[x]
   i=random.randint(1,N)  
   for x in dict:
     if i<=dict[x]:
       return x
     else:
       i=i-dict[x]   

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
       
 def cutsize(self,i):# i is an integer between 1 and 2^n-2, with n the number of vertices
  present={}
  for x in self.adj:
    if i%2==1:
      present[x]=True
    i=i>>1
  res=0  
  for x,y in self.adj.items():
     for t,u in y.items():
         if x in present and not t in present:
            res+=u
  return [res,[x for x in present]]

   
 def contract(self,i,j):# contracts edge i,j (i absorbs j)
  mult_edge=self.adj[i][j]
  del self.adj[j][i]
  del self.adj[i][j]
  self.deg[i]-=mult_edge
  for x,y in self.adj[j].items():
    if x in self.adj[i]:
      self.adj[i][x]+=y
      self.adj[x][i]+=y
    else:
      self.adj[i][x]=y
      self.adj[x][i]=y
    del self.adj[x][j]
    self.deg[i]+=y
  del self.adj[j]
  del self.deg[j] 
 
 def random_vertex(self):
  return random_element(self.deg)
   
 def random_edge(self):
  i=self.random_vertex()
  j=random_element(self.adj[i])
  return (i,j)
 
 def display(self):
  for x,y in self.adj.items():
    print("Neighbours of "+str(x)+", which has degree "+str(self.deg[x]))	
    for t,u in y.items(): 
      print(str(t)+" with multiplicity "+str(u))
