import math
import random
import time
## Question 5 ##
def random_element(dict):
    # TO COMPLETE
   elements=0
   for v in dict.values():
     elements+=v
   i=random.randint(1,elements)  
   for key in dict:
     if i>dict[key]:
       i-=dict[key]
     else:
       return key 

## Question 7 ##
def random_cut(m):
    # TO COMPLETE
    part=dict()
    for key in m.deg.keys():
        part[key]=[]
    while len(m.deg)>2:
        (i,j) = m.random_edge()
        part[i].append(j)
        for x in part[j]:
            part[i].append(x)
        del part[j]
        m.contract(i,j)
    for deg in m.deg:
        return m.deg[deg],[deg]+part[deg]
    
def mincut_karger(L, p): # p is the desired error bound
    # TO COMPLETE
    n=L[0]
    k=math.ceil(math.log(p)/(math.log(1-2/(n*(n-1)))))
    m=10**9
    for i in range(k):
        graph=MultiGraph(L)
        (a,b)=random_cut(graph)
        if a<m:
            m=a
    return m

## Contains Questions 4 and 6 ##
class MultiGraph:
    def __init__(self, L):
        self.adj = {}
        self.deg = {}
        for x in L[1]:
            if x[0] not in self.adj:
                self.adj[x[0]] = {x[1]: x[2]}
                self.deg[x[0]] = x[2]
            else:
                self.adj[x[0]][x[1]] = x[2]
                self.deg[x[0]] += x[2]
            if x[1] not in self.adj:
                self.adj[x[1]] = {x[0]: x[2]}
                self.deg[x[1]] = x[2]
            else:
                self.adj[x[1]][x[0]] = x[2]
                self.deg[x[1]] += x[2]

    def subset_from_integer(self, i):# i is an integer between 1 and 2^n - 2, with n the number of vertices
        subset = {}
        for x in self.adj:
            if i % 2 == 1:
                subset[x] = True
            i = i >> 1
        return subset

    def cutsize(self, i):# i is an integer between 1 and 2^n - 2, with n the number of vertices
        subset = self.subset_from_integer(i)
        res = 0
        for x, y in self.adj.items():
            for t, u in y.items():
                if x in subset and not t in subset:
                    res += u
        return [res, [x for x in subset]] 

    def display(self):
        for x, y in self.adj.items():
            print("Neighbors of " + str(x) + ", which has degree " + str(self.deg[x]))	
            for t, u in y.items(): 
                print(str(t) + " with multiplicity " + str(u))
    
    ## Question 4 ##
    def contract(self, i, j):# contracts edge i, j (i absorbs j)
        # TO COMPLETE
        for (k,v) in self.adj[j].items():
            if k==i:
                self.deg[i]-=v
            elif k in self.adj[i]:
                self.deg[i]+=v
                self.adj[k][i]+=v
                self.adj[i][k]+=v
            else:
                self.deg[i]+=v
                self.adj[k][i]=v
                self.adj[i][k]=v

        for key in self.adj.keys():
            if j in self.adj[key]:
                del self.adj[key][j]
        del self.deg[j]
        del self.adj[j]

    ## Question 6.1 ##
    def random_vertex(self):
        # TO COMPLETE
        rand = random_element(self.deg)
        return rand

    ## Question 6.2 ##
    def random_edge(self):
        # TO COMPLETE
        i = self.random_vertex()
        return (i,random_element(self.adj[i]))

