from DG import *

def contains_pattern(s,text):
  sp="(.)*"+s+"(.)*"
  print(sp)
  nfa=NFA(sp)
  return nfa.check_text(text)

class NFA:
  def __init__(self,s): # s is the string containing the regular expression
    self.s=s
    self.m=len(self.s)
    self.dg=DG(len(s)+1) # the directed graph that stores the epsilon links
    self.lp=[-1 for _ in range(len(s))]
    self.rp=[-1 for _ in range(len(s))]
    self.left_right_match_or() # assigns lp and rp according to parentheses matches
    self.build_eps_links() # assigns the epsilon links in self.dg

  def left_right_match(self):
    stack=[]
    for i in range(self.m):
       if self.s[i]=='(':
          stack.append(i)
       elif self.s[i]==')':
          j=stack.pop()
          self.lp[i]=j
          self.rp[j]=i

  def left_right_match_or(self):
    stack=[]
    for i in range(self.m):
       if self.s[i]=='(' or self.s[i]=='|':
          stack.append(i)
       elif self.s[i]==')':
          j=stack.pop()
          if self.s[j]=='|':
             k=stack.pop()
             self.lp[i]=k; self.rp[k]=i; self.lp[j]=k; self.rp[j]=i
          else:
             self.lp[i]=j
             self.rp[j]=i
  
  def left_right_match_multior(self):
    stack=[]
    for i in range(self.m):
       if self.s[i]=='(' or self.s[i]=='|':
          stack.append(i)
       elif self.s[i]==')':
          j=stack.pop() 
          or_positions=[]     
          while self.s[j]=='|':
             or_positions.append(j)
             self.rp[j]=i
             j=stack.pop()
          for b in or_positions:
             self.lp[b]=j; self.rp[b]=i 
          self.lp[i]=j
          self.rp[j]=i

  def build_eps_links(self):
     for i in range(self.m):
       if self.s[i]=='(' or self.s[i]==')' or self.s[i]=='*':
         self.dg.add_link(i,i+1)
     for i in range(self.m):
       if self.s[i]=='|':
         self.dg.add_link(self.lp[i],i+1)
         self.dg.add_link(i,self.rp[i])
       if self.s[i]=='*':
         j=self.lp[i-1]
         self.dg.add_link(i,j)
         self.dg.add_link(j,i)

  def check_text(self,w):
     accessible=self.dg.explore_from_subset([0])     
     for i in range(len(w)):
        states_after_reading_letter=[]
        for j in accessible:
            if j==self.m: continue
            if self.s[j]=='.' or self.s[j]==w[i]:
               states_after_reading_letter.append(j+1)
        if(len(states_after_reading_letter))==0: return False
        accessible=self.dg.explore_from_subset(states_after_reading_letter)
     return self.m in accessible   

'''
For each character of w one has to run an exploration of the directed graph of eps-links.
This graph has m+1 vertices and has O(m) edges, since each vertex has at most 4 neighbours. 
Hence the complexity of each exploration (DFS algorithm, cf CSE103) has complexity O(m).
Hence, the overall complexity is O(mn).
'''

  




 
