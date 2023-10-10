
import collections,math

def shortest_route_len(G, s, t):
    q= collections.deque([s])
    n=len(G)
    d=[]
    for i in range(n):
        if i==s:
            d.append(0)
        else:
           d.append(math.inf)
    while q:
        c = q.popleft()
        if c == t:
            return d[t]
        for l in G[c]:
            if d[l]!= math.inf:
                continue
            d[l] = d[c]+1
            q.append(l)
    return math.inf


