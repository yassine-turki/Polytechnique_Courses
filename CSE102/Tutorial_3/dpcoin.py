def transacts_num(n):
    cache = {}
    cache[0] = 0
    for i in range(1, n+1):
        l=[]
        for v in [1,3,7,9] :
            if i-v >= 0:
                l.append(1 +cache[i-v])
        cache[i]=min(l)
               
    return cache[n]