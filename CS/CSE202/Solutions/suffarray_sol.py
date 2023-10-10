# -*- coding: utf-8 -*-

def str_compare(a, b):
    N = min(len(a),len(b))
    for i in range(N):
        if a[i] < b[i]:
            return -1
        elif a[i] > b[i]:
            return 1

    return len(a)-len(b)

def str_compare_m(a,b, m):
    if len(a) >= m and len(b) >= m:
        # len(a) >= m and len(b) >= m
        return str_compare(a[:m], b[:m])
    else:
        # len(a) < m or len(b) > m
        return str_compare(a,b)

def longest_common_prefix(a, b):
    N = min(len(a),len(b))
    for i in range(N):
        if a[i] != b[i]:
            return i
    return N

    
class suffix_array:
    def __init__(self, t):
        self.T = t
        self.N = len(t)
        self.suffId = [i for i in range(self.N)]
         
        self.suffId.sort(key=lambda i: self.T[i:])
        
    def suffix(self, i):
        return self.T[self.suffId[i]:]
        
    def findL(self, S):
        m = len(S)
        l = -1
        r = self.N
        while r != l + 1:
            mid = (l + r) // 2
            c = str_compare_m(S, self.suffix(mid), m)
            if c <= 0:
                r = mid
            else:
                l = mid
        return r
        
    def findR(self,S):
        m = len(S)
        l = -1
        r = self.N
        while r != l + 1:
            mid = (l + r) // 2
            c = str_compare_m(self.suffix(mid), S, m)
            if c <= 0:
                l = mid
            else:
                r = mid
        return r

    def findLR(self,S):
        return (self.findL(S),self.findR(S))

def KWIC(sa, S, c = 15):
    m = len(S)
    (L,R) = sa.findLR(S)
    res = []
    for i in range(L,R):
        j = sa.suffId[i]
        l = max(0, j - c)
        r = min(sa.N, j + m + c)
        res.append(sa.T[l:r])
    return res
    
def longest_repeated_substring(sa):
    m = 0
    best_i = -1
    for i in range(0, sa.N-1):
        res = longest_common_prefix(sa.suffix(i), sa.suffix(i+1))
        if res > m:
            m = res
            best_i = i
    return sa.suffix(best_i)[0:m]