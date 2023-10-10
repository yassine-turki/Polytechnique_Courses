from MultiGraph_sol import *
import math
import time

def mincut_brute(m):
  n=len(m.adj)
  best=[math.inf]
  for i in range(1,2**n-1,2):
    cut=m.cutsize(i)
    if cut[0]<best[0]:
     best=cut
  return best
  
def random_cut(m):
  n=len(m.adj)
  partition={}
  for x in m.adj:
    partition[x]=[]
  for _ in range(n-2):
    (i,j)=m.random_edge()
    m.contract(i,j)
    partition[i]=partition[i]+[j]+partition[j]
    del(partition[j])
  x=next(iter(partition))
  return [m.deg[x],[x]+partition[x]] 
    
def mincut_karger(L,e): # e is the wished error bound
  n=L[0]
  p=2/n/(n-1) # proba success at each trial is at least p
  k=math.ceil(math.log(e)/math.log(1-p)) # number of trials so that P(error)<=e
  print("Number of trials Karger: "+str(k))
  start = time.time()
  best=math.inf
  best_cut=[]
  for _ in range(k):
    m=MultiGraph(L)
    res_trial= random_cut(m)
    if res_trial[0]<best:
      best=res_trial[0]
      best_cut=res_trial[1]
  elapsed = (time.time() - start)  
  print("Running time: "+str(elapsed))
  print("Average time per trial: "+str(elapsed/k))
  return [best,best_cut]   
