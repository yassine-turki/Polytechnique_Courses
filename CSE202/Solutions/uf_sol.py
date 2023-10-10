# -*- coding: utf-8 -*-

class UF_base:
    '''
        basic Union-Find implementation, implementing Quick-find
    '''
    def __init__(self, N):
        self.N = N
        self.A = [i for i in range(N)]
        self.count = N
    
    def get_N(self):
        return self.N
        
    def get_count(self):
        return self.count
    
    def union(self,p,q):
        if self.is_connected(p,q):
            return

        # merging the classes of p and q
        self.count -= 1            
        r1 = self.find(p)
        r2 = self.find(q)
        
        # all the elements with root r2 now has root r1
        for i in range(self.N):
            if self.A[i] == r2:
                self.A[i] = r1
        
    def find(self, p):
        return self.A[p]
            
    def is_connected(self, p, q):
        return self.find(p) == self.find(q)
        
class Rank_UF(UF_base):
    def __init__(self,N):
        super().__init__(N)
        self.ranks = [1 for _ in range(N)]
        
    def union(self, p, q):
        '''
            TO IMPLEMENT
        '''
        r1 = self.find(p)
        r2 = self.find(q)
        
        if r1 == r2:
            return
            
        self.count -= 1
        
        if self.ranks[r2] > self.ranks[r1]:
            self.A[r1] = r2
        else:
            self.A[r2] = r1
            
        if self.ranks[r2] == self.ranks[r1]:
            self.ranks[r1] += 1
        
    def find(self, p):
        '''
            TO IMPLEMENT
        '''
        if self.A[p] == p:
            return p
        # path compression
        self.A[p] = self.find(self.A[p])
        return self.A[p]        