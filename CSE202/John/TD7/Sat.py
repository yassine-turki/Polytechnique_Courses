# -*- coding: utf-8 -*-
import random

class Sat:
      
  def __init__(self,n,L):
    self.nr_var=n   # variables are x1,...,xn
    self.clauses=L
    self.values=[True for i in range(n+1)] # position 0 in this list is not used
    self.fixed={}
    

  def is_clause_satisfied(self,c):
      k=False
      
      for i in c:
                  if i > 0: 
                      if self.values[i]==True:        
                          k =True
                  else:
                      if self.values[-i]==False:        
                          k = True                                         
      return k
                  
    
 ##DOES NOT WORK       
  def satisfied(self):
      k = True 
      for clause in self.clauses:
          if self.is_clause_satisfied(clause) == False:
             k= False 
          
      return k      
            
         
  def initialize(self):
    for i in range(self.nr_var):
        if i not in self.fixed:
            self.values[i] = random.choice([True, False])
        
          
  def walk_sat(self,N):
      self.clauses.sort(key=len) 
      self.initialize()
      
      n =0
      
      while not self.satisfied():
          if n%N == 0 :
              self.initialize()

          i=0
          
          while self.is_clause_satisfied(self.clauses[i]) == True and i < len(self.clauses)-1:
              i +=1
           
            
          k = abs(random.choice(self.clauses[i]))
          self.values[k]= not self.values[k]
          
          n+=1
          
          
   
  ##################################################
  # PROPAGATION METHODS
  ##################################################  
   
  def fix_values_from_1clauses(self):
    K = False
    for clause in self.clauses:
        if len(clause) == 1:
            if clause[0] > 0:
                
                self.fixed[abs(clause[0])] = True
            else:
                
                self.fixed[abs(clause[0])] = False
            
            K=True
            
    return K
            
        
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
     c = self.fix_values_from_1clauses()
     while c: 
         self.clauses = self.simplify_clauses()
         c = self.fix_values_from_1clauses()  
       
         
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

            


# # -*- coding: utf-8 -*-
# import random

# class Sat:
#     def __init__(self,n,L):
#         self.nr_var=n   # variables are x1,...,xn
#         self.clauses=L
#         self.values=[True for i in range(n+1)] # position 0 in this list is not used
#         self.fixed={}
        
#     def is_clause_satisfied(self,c):
#         arr = []
#         for e in c:
#             if e < 0:
#                 if self.values[-e] == True:
#                     arr.append(False)
#                 else:
#                     arr.append(True)
#             else:
#                 if self.values[e] == False:
#                     arr.append(False)
#                 else:
#                     arr.append(True)
#         for i in range(len(arr)):
#             if arr[i] == True:
#                 return True
#         else:
#             return False

        
#     def satisfied(self):
#         for c in self.clauses:
#             if self.is_clause_satisfied(c) == False:
#                 return False
#         else:
#             return True 

#     def initialize(self):
#         self.values = [random.choice([True, False]) for _ in range(self.nr_var+1)]
#         pass
      
#     # def walk_sat(self,N):
#     #     while True:
#     #         self.clauses.sort(key=len)
#     #         self.initialize()
#     #         for i in range(N):
#     #             if self.satisfied():
#     #                 return None
#     #             else:
#     #                 for c in self.clauses:
#     #                     if not self.is_clause_satisfied(c):
#     #                         not_satisfied_clause = c
#     #                         break
#     #                 index_x = random.randrange(0, len(not_satisfied_clause))
#     #                 j = abs(c[index_x]) # we use abs in order to have a j > 0 when looking for xj in self.values
#     #                 if self.values[j]:
#     #                     self.values[j] = False
#     #                 else:
#     #                     self.values[j] = True
#     def walk_sat(self,N):
#       self.clauses.sort(key=len) 
#       self.initialize()
      
#       n =0
      
#       while not self.satisfied():
#           if n%N == 0 :
#               self.initialize()

#           i=0
          
#           while self.is_clause_satisfied(self.clauses[i]) == True and i < len(self.clauses)-1:
#               i +=1
           
            
#           k = abs(random.choice(self.clauses[i]))
#           self.values[k]= not self.values[k]
          
#           n+=1
        
#   ##################################################
#   # PROPAGATION METHODS
#   ##################################################  
   
#     def fix_values_from_1clauses(self):
#         b = False
#         for c in self.clauses:
#             if len(c) == 1:
#                 #b = True
#                 if c[0] < 0:
#                     self.fixed[abs(c[0])] = False
#                     # self.values[abs(c[0])] = False
#                 else:
#                     self.fixed[abs(c[0])] = True 
#                     #self.values[abs(c[0])] = True
#                 b = True 
#         return b
        

        
#     def simplify_clause(self,c):
#       res=[]
#       for x in c:
#           if not abs(x) in self.fixed:
#               res.append(x)
#           else:
#               if (x>0 and self.values[x]) or (x<0 and not self.values[-x]):
#                   return -1
#       return res   

#     def simplify_clauses(self):
#       res=[]    
#       for c in self.clauses:  
#          cp=self.simplify_clause(c)
#          if not cp==-1:
#              res.append(cp)
#       return res        
    
#     def simplify_formula_by_propagation(self):
#         b = self.fix_values_from_1clauses()
#         while b :
#             self.clauses = self.simplify_clauses()
#             b = self.fix_values_from_1clauses()


#   ##################################################
#   # DISPLAY METHODS
#   ##################################################                      
                                  
#     def clause_to_string(self,c):
#        res="" 
#        for i in range(0,len(c)):
#            if i==0: res="("
#            else: res=res+" ∨ "
#            if(c[i]>0): res=res+"x"+str(c[i])
#            else: res=res+"¬x"+str(-c[i])
#        return res+")"
     
#     def display_statistics(self):
#         print("Number of clauses: "+str(len(self.clauses)))
#         print("Number of non-fixed variables: "+str(self.nr_var-len(self.fixed)))
#         print("")

#     def display_formula(self):
#        L=self.clauses
#        res=self.clause_to_string(L[0])
#        for i in range(1,len(L)):     
#            res=res+" ∧ "+self.clause_to_string(L[i])   
#        print(res)    
              
#     def display_values(self):
#        res="" 
#        for i in range(1,self.nr_var+1):
#            res=res+"x"+str(i)+"="+str(self.values[i])+" "
#        print(res)    

            
