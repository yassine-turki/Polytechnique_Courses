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
    # Question 1
    def __init__(self, t):
        self.T = t
        self.N = len(t)
        self.suffId = [i for i in range(self.N)]
        self.suffId.sort(key= lambda k: self.T[k:])

        # TODO: order suffId by lexicographic order
        # SORT

    def suffix(self, i):
        return self.T[self.suffId[i]:]

    # Question 2
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

    # Question 2
    def findR(self,S):
        # TO IMPLEMENT
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

# Question 4
def KWIC(sa, S, c = 15):
    # TO IMPLEMENT
    (l,r) = sa.findLR(S)
    occurences = []
    for i in range(l,r):
        suffix = sa.suffId[i]
        start= suffix-c if suffix-c>0 else 0
        stop= sa.N if sa.N<suffix+c+len(S) else suffix+c+len(S)
        occurences.append(sa.T[start:stop])
    return occurences 

# Question 5
def longest_repeated_substring(sa):
    # TO IMPLEMENT
    k=0
    idx = -1
    for i in range((sa.N)-1):
        lcp = longest_common_prefix(sa.suffix(i), sa.suffix(i+1))
        if lcp > k:
            k = lcp
            idx = i 
    result =sa.suffix(idx)[0:k]
    return result
