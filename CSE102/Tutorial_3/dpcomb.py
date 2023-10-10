def binom_td(n, k, cache = None):
    cache = {} if cache is None else cache
    if (n,k) in cache:
        return cache[n,k]
    else:
        if k == 0:
            return 1
        elif k > n:
            return 0
        else:
            a=binom_td(n-1,k,cache) + binom_td(n-1,k-1,cache)
            cache[n,k]=a
        return cache[n,k]

def parts_td(n, k = None, cache = None):
    cache = {} if cache is None else cache
    if k is None:
        return sum(parts_td(n,i,cache) for i in range(1,n+1))
    if (n,k) in cache:
        return cache[n,k]
    else:
        if k==1:
            return 1
        elif k>n:
            return 0 
        else:
            a=parts_td(n-1,k-1,cache) + parts_td(n-k,k,cache)
            cache[n,k]=a
            return a
        
def parts_bu(n):
    cache = [[0 for _ in range(n+1)] for _ in range(n+1)]
    a=0
    for i in range(1,n+1):
        cache[i][1] = 1
        for v in range(2,i+1):
            cache[i][v] = cache[i-1][v-1] + cache[i-v][v]
    for k in range(1,n+1):
        a+=cache[i][k]
    return a