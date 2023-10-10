from MultiGraph import *
import math

def mincut_brute(m):
    n = len(m.adj)
    best = [math.inf]
    for i in range(1, 2**n-1, 2):
        cut = m.cutsize(i)
        if cut[0] < best[0]:
            best = cut
    return best 
        
  

def random_cut(m):
   n=len(m.adj)
   partition = {}
   for x in m.adj:
     partition[x] = []
   for _ in range(n-2):
       (i,j) = m.random_edge()
       m.contract(i,j)
       partition[i] += [j] + partition[j]
       del(partition[j])
   x=next(iter(partition))
   return [m.deg[x],[x]+partition[x]] 
    
    
def mincut_karger(L,e): # e is the wished error bound
    n = L[0]
    p = 2/n/(n-1)
    k = math.ceil(math.log(e) / math.log(1-p))
    best = math.inf
    best_cut = []
    for _ in range(k):
        m = MultiGraph(L)
        res = random_cut(m)
        if res[0] < best:
            best = res[0]
            best_cut = res[1]
    return [best, best_cut]
