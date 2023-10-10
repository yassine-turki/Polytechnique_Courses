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
            
        self.suffId.sort(key= lambda k: self.T[k:])
        
    def suffix(self, i):
        return self.T[self.suffId[i]:]
        
    def findL(self, S):
        l = -1
        r = self.N
        while r != l+1:
            k = (l+r) // 2
            if str_compare_m(S, self.suffix(k), len(S)) <= 0: 
                r = k
            else:
                l = k
        return r
        
    def findR(self,S):
        l = -1
        r = self.N
        while r != l+1:
            k = (l+r) //2
            if str_compare_m(self.suffix(k), S,  len(S)) <= 0:
                l = k
            else:
                r = k
        return r

    
    def findLR(self,S):
        return (self.findL(S),self.findR(S))

def KWIC(sa, S, c = 15):
    L,R = sa.findLR(S)
    li = []
    for i in range(L,R):
        suff = sa.suffId[i]
        left = max(0, suff - c)
        right = min(sa.N, suff + c + len(S))
        li.append(sa.T[left:right])
    return li 
        
    
def longest_repeated_substring(sa):
    m = 0
    index = -1
    for i in range(0, sa.N-1):
        tmp = longest_common_prefix(sa.suffix(i), sa.suffix(i+1))
        if tmp > m:
            m = tmp
            index = i 
    return sa.suffix(index)[0:m]

