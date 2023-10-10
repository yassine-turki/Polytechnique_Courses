# -*- coding: utf-8 -*-
import random

class Sat:
      
  def __init__(self,n,L):
    self.nr_var=n   # variables are x1,...,xn
    self.clauses=L
    self.values=[True for i in range(n+1)]    
    self.fixed={}
    
  def is_clause_satisfied(self,c): 
    for x in c:
        if x>0 and self.values[x]:
            return True
        if x<0 and not self.values[-x]:
            return True
    return False
        
  def satisfied(self):
    for c in self.clauses:
        if not self.is_clause_satisfied(c):
            return False
    return True
         
  def initialize(self):
      for i in range(1,self.nr_var+1):
          if not i in self.fixed:
              self.values[i]=random.choice([True, False])
         
  def walk_sat(self,N):
     if N==0: return 
     self.clauses.sort(key=len)
     i=0
     satisfied=False
     while not satisfied:
        if i%N==0: 
            self.initialize()
        satisfied=True    
        for c in self.clauses:
           if not self.is_clause_satisfied(c):
             satisfied=False  
             s=random.randint(0,len(c)-1)
             r=abs(c[s])
             self.values[r]=not self.values[r] 
             break 
        i=i+1
     print("WalkSat statistics:")   
     print("Number of times walk_sat has restarted: "+str(i//N))
     print("Number of iterations at each trial (value of N): "+str(N))
     print("Number of iterations in successful trial: "+str(i%N))
     print("")
     
  def fix_values_from_1clauses(self):
    found1clause=False  
    for c in self.clauses:
        if len(c)==1:
            found1clause=True
            x=c[0]
            if x>0:
                self.values[x]=True
                self.fixed[x]=True
            else:
                self.values[-x]=False
                self.fixed[-x]=False
    return found1clause    
        
  def simplify_clause(self,c):
    res=[]
    for x in c:
        if not abs(x) in self.fixed:
            res.append(x)
        else:
            if (x>0 and self.values[x]) or (x<0 and not self.values[-x]):
                return -1
    return res   

  def simplify_clauses(self):
    res=[]    
    for c in self.clauses:  
       cp=self.simplify_clause(c)
       if not cp==-1:
           res.append(cp)
    return res        
    
  def simplify_formula_by_propagation(self):                                  
     donext=True  
     while donext:    
       donext=self.fix_values_from_1clauses()
       if donext:
          self.clauses=self.simplify_clauses()  

  ##################################################
  # DISPLAY METHODS
  ##################################################                      
                                  
  def clause_to_string(self,c):
     res="" 
     for i in range(0,len(c)):
         if i==0: res="("
         else: res=res+" ∨ "
         if(c[i]>0): res=res+"x"+str(c[i])
         else: res=res+"¬x"+str(-c[i])
     return res+")"
     
  def display_statistics(self):
      print("Number of clauses: "+str(len(self.clauses)))
      print("Number of non-fixed variables: "+str(self.nr_var-len(self.fixed)))
      print("")

  def display_formula(self):
     L=self.clauses
     res=self.clause_to_string(L[0])
     for i in range(1,len(L)):     
         res=res+" ∧ "+self.clause_to_string(L[i])   
     print(res)    
              
  def display_values(self):
     res="" 
     for i in range(1,self.nr_var+1):
         res=res+"x"+str(i)+"="+str(self.values[i])+" "
     print(res)    

            
