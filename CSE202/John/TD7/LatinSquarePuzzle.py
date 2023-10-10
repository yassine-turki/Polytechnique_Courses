# -*- coding: utf-8 -*-
from Sat import *

class LatinSquarePuzzle:
    def __init__(self,k,initial):
      self.k=k  
      self.initial=initial
      self.sat=Sat(self.k**3,[])   
      self.final=[]
        
    def triple_to_int(self,v,i,j):
        return 1+i*self.k**2+j*self.k+v
        
    def int_to_triple(self,r):    
        v=(r-1)%self.k
        j=((r-1)//self.k)%self.k
        i=((r-1)//self.k**2)%self.k
        return [v,i,j]
        
    def build_generic_clauses(self):
        for i in range(self.k):
            for j in range(self.k):
                clause = []
                clause1 = []
                for v in range(self.k):
                    clause.append(self.triple_to_int(v, i, j))
                    clause1.append( - self.triple_to_int(v, i, j))
                self.sat.clauses.append(clause)
                self.sat.clauses.append(clause1)
                
        for v in range(self.k):
            for i in range(self.k):
                clause = []
                clause1 = []
                for j in range(self.k):
                    clause.append(self.triple_to_int(v, i, j))
                    clause1.append( - self.triple_to_int(v, i, j))
                self.sat.clauses.append(clause)
                self.sat.clauses.append(clause1)
        
        for v in range(self.k):
            for j in range(self.k):
                clause = []
                clause1 = []
                for i in range(self.k):
                    clause.append(self.triple_to_int(v, i, j))
                    clause1.append( - self.triple_to_int(v, i, j))
                self.sat.clauses.append(clause)
                self.sat.clauses.append(clause1)
    
    
    def add_fixed_value_clauses(self):
        for i in range(self.k):
            for j in range(self.k):
                if self.initial[i][j] != "*":
                    self.sat.clauses.append([self.triple_to_int(self.initial[i][j], i, j)])
                    
    def solve(self):
       self.build_generic_clauses()
       self.add_fixed_value_clauses()
       self.sat.simplify_formula_by_propagation()       
       n = self.sat.nr_var       
       f=self.sat.nr_var-len(self.sat.fixed)       
       if f>0:
           N=4*f**2  
           self.sat.walk_sat(N)
       
       self.final = self.initial
       for x in range(1,self.sat.nr_var+1):
           if self.sat.values[x] == True:              
               [v,i,j] = self.int_to_triple(x)
               self.final[i][j] = v
         
    ##################################################
    # DISPLAY METHODS
    ##################################################      
     
    def display_before_solving(self):
        print("Initial configuration:")
        for r in range(self.k): 
            print("[{0}]".format(', '.join(map(str, self.initial[r]))))
        print("")    

    def display_after_solving(self):
        if(len(self.final)==0):
            print("Not yet solved")
            return
        print("Solved configuration:")
        for r in range(self.k):    
            print("[{0}]".format(', '.join(map(str, self.final[r]))))
        print("")     