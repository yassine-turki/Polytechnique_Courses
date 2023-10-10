# -*- coding: utf-8 -*-
from Sat import *
import math

class LatinSquarePuzzle:
    def __init__(self,k,initial):
      self.k=k  
      self.initial=initial
      self.sat=Sat(self.k**3,[])   
      self.final=[]
      self.sudoku_mode=False
        
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
                self.sat.clauses.append([self.triple_to_int(v,i,j) for v in range(self.k)])
                self.sat.clauses.append([self.triple_to_int(j,v,i) for v in range(self.k)])
                self.sat.clauses.append([self.triple_to_int(i,j,v) for v in range(self.k)])
                for v1 in range(1,self.k):
                    for v2 in range(v1):
                        self.sat.clauses.append([-self.triple_to_int(v1,i,j), -self.triple_to_int(v2,i,j)])
                        self.sat.clauses.append([-self.triple_to_int(j,v1,i), -self.triple_to_int(j,v2,i)])
                        self.sat.clauses.append([-self.triple_to_int(i,j,v1), -self.triple_to_int(i,j,v2)])            
                
    def add_sudoku_clauses(self):# only when k is a square number
        r=round(math.sqrt(self.k))
        if r**2!=self.k: print("Error: matrix length has to be a square number"); pass
        for ir in range(r):
            for jr in range(r): # choice of the subsquare
                 entries=[[ir*r+i,jr*r+j] for i in range(r) for j in range(r)] # list of entries in the chosen subsquare               
                 for v in range(self.k):                    
                     self.sat.clauses.append([self.triple_to_int(v,x[0],x[1]) for x in entries])
                     for e1 in range(1,self.k):
                         for e2 in range(e1):
                              x1=entries[e1]; x2=entries[e2]
                              p=self.triple_to_int(v,x1[0],x1[1])
                              q=self.triple_to_int(v,x2[0],x2[1])
                              self.sat.clauses.append([-p,-q])          
                     
            
    def add_fixed_value_clauses(self):
        for i in range(self.k):
            for j in range(self.k):
                v = self.initial[i][j]
                if v != '*': 
                    self.sat.clauses.append([self.triple_to_int(v,i,j)])
                              
    def solve(self):
         self.build_generic_clauses()
         if self.sudoku_mode:
             self.add_sudoku_clauses()
         self.add_fixed_value_clauses()
         print("Before propagation:")
         self.sat.display_statistics()
         self.sat.simplify_formula_by_propagation()
         print("After propagation:")
         self.sat.display_statistics()
         f=self.sat.nr_var-len(self.sat.fixed)
         if f>0:
           N=4*f**2  
           self.sat.walk_sat(N)
         res=[['*' for _ in range(self.k)] for __ in range(self.k)]
         for r in range(1,self.sat.nr_var+1):
            if self.sat.values[r]:
                [v,i,j]=self.int_to_triple(r)
                if(res[i][j]!='*'):
                    print("error: at most one value per entry")
                    return
                res[i][j]=v
         self.final=res 
         
    ##################################################
    # DISPLAY METHODS
    ##################################################       
     
    def display_before_solving(self):
        print("Initial configuration:")
        for r in range(self.k):
            #print(self.initial[r]) 
            print("[{0}]".format(', '.join(map(str, self.initial[r]))))
        print("")

    def display_after_solving(self):
        if(len(self.final)==0):
            print("Not yet solved")
            return
        print("Solved configuration:")
        for r in range(self.k):
            # print(self.final[r])     
            print("[{0}]".format(', '.join(map(str, self.final[r]))))
        print("")
