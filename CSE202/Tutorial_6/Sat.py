# -*- coding: utf-8 -*-
import random

class Sat:

    def __init__(self,n,L):
        self.nr_var=n   # variables are x1,...,xn
        self.clauses=L
        self.values=[True for i in range(n+1)] # position 0 in this list is not used
        self.fixed={}

  # Question 1

    def is_clause_satisfied(self,c):
          # TO COMPLETE  
        for clause in c:
            if clause < 0:
                if self.values[-clause] == False:
                    return True
            if clause > 0 :
                if self.values[clause] == True:
                    return True
        return False

    def satisfied(self):
        # TO COMPLETE
        for clause in self.clauses:
            if self.is_clause_satisfied(clause)==False:
                return False
        return True
    # Questions 2 & 8

    def initialize(self):
        # TO COMPLETE
        n=self.nr_var
        for i in range(1,n+1):
            if i not in self.fixed:
                self.values[i] = random.choice([True, False])

    def walk_sat(self,N):
        #TO COMPLETE
        self.initialize()
        self.clauses.sort(key = len)
        for i in range(N):
            wrongclause = -1
            for i, c in enumerate(self.clauses):
                if self.is_clause_satisfied(c)==False:
                    flip = abs(random.choice(c))
                    self.values[flip] = not self.values[flip]
                    wrongclause = i
                    break
            if wrongclause == -1:
                break

    ##################################################
    # PROPAGATION METHODS
    ##################################################  

    # Question 6

    def fix_values_from_1clauses(self):
        # TO COMPLETE
     BOOL=False  
     for clause in self.clauses:
        if len(clause)==1:
            BOOL=True
            c=clause[0]
            if c<0:
                self.values[-c]=False
                self.fixed[-c]=False
            else:
                self.values[c]=True
                self.fixed[c]=True
                
     return BOOL 
    # Helper functions for Question 7

    def simplify_clause(self,c):
        l=[]
        for clause in c:
            if  not abs(clause) in self.fixed:
                l.append(clause)
            else:
                if (clause<0 and self.values[-clause]==False) or (clause>0 and self.values[clause]==True):
                    return -1
        return l   

    def simplify_clauses(self):
        l=[]    
        for clause in self.clauses:  
            simpc=self.simplify_clause(clause)
            if not simpc==-1:
                l.append(simpc)
        return l        

    # Question 7

    def simplify_formula_by_propagation(self):
        # TO COMPLETE
        while self.fix_values_from_1clauses():
            self.clauses = self.simplify_clauses()

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
