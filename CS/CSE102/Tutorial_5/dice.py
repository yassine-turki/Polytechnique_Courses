import random

def roll(D):
    l=[]
    s=0
    i=len((D))
    rand = random.random()
    for p in D:
        l.append(s)
        s += p
    while rand < l[i-1]:
        i -= 1
    return i
    
def rolls(D, N):
    n=len(D)
    l = [0]*n
    for i in range(N):
        l[roll(D)-1]+=1
    return l
