from DG import *

def contains_pattern(s,text):
  sp="(.)*"+s+"(.)*"
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
        
    def __str__(self):
        n = self.m
        str_lp = 'lp: '
        str_rp = 'rp: '
        for i in range(self.m):
            if self.lp[i]==-1:
                str_lp += '-1  '
            elif self.lp[i]<10:
                str_lp += str(self.lp[i]) + '   '
            else: str_lp += str(self.lp[i]) + '  '
            if self.rp[i]==-1:
                str_rp += '-1  '
            elif self.rp[i]<10:
                str_rp += str(self.rp[i]) + '   '
            else: str_rp += str(self.rp[i]) + '  '
        str_lp += '\n'
        str_rp += '\n'
        
        str_dg = str(self.dg)
        
        s = '------------------\nRegular expression\n------------------\n' + 're: ' + '   '.join(self.s) + '\n'
        return s + str_lp + str_rp #+ '------------------\nCorresponding NFA\n------------------\n' + str_dg 

    def left_right_match(self):
        stack = []
        for i in range(self.m):
            if self.s[i] == '(':
                stack.append(i)
            elif self.s[i] == ')':
                index = stack.pop()
                self.rp[index] = i 
                self.lp[i] = index
            
    def left_right_match_or(self):
        stack = [] 
        for i in range(self.m):
            if self.s[i] == '(' or self.s[i] == '|':
                stack.append(i)
            elif self.s[i] == ')':
                index = stack.pop()
                if self.s[index] == '|':
                    new_index = stack.pop()
                    self.rp[index] = i 
                    self.rp[new_index] = i 
                    self.lp[index] = new_index
                    self.lp[i] = new_index
                    
                else:
                    self.rp[index] = i 
                    self.lp[i] = index
                
            
    
    def left_right_match_multior(self):    
        "OPTIONAL"
        pass
    
    def build_eps_links(self):
        e_links = {"(", ")", "*"}
        for i in range(self.m):
            if self.s[i] in e_links:
                self.dg.add_link(i, i+1)
        for i in range(self.m):
            if self.s[i] == '|':
                self.dg.add_link(self.lp[i], i+1)
                self.dg.add_link(i, self.rp[i])
            if self.s[i] == "*":
                self.dg.add_link(self.lp[i-1], i)
                self.dg.add_link(i, self.lp[i-1])


    def check_text(self,w):
        #K is the set of vertices we can go to from the initial position (e-links)
        K = self.dg.explore_from_subset([0])
        n = len(w)
        for i in range(n):
            K_after_consuming_word = [] 
            # This set is the set of vertices we can go to after following all the
            #possible links from the set K 
            for j in K:
                if j == self.m : continue 
                # if the vertex we can go is equal to len(self.s) we already have expression matching. 

                if self.s[j] == '.' or self.s[j] == w[i]:
                    #If we can go to any letter ('.' link) or if the letters are equal (black links)
                    K_after_consuming_word.append(j+1)
            if len(K_after_consuming_word) == 0: 
                return False
            #If we couldn't go to another vertex after initial state then there is no possible matching 
            K = self.dg.explore_from_subset(K_after_consuming_word)
            #We repeat the process to get all the vertices accessible from the newly acessed vertices. 
        return self.m in K #as soon as we have an index that is equal to the length of the word we have matching. 
            
            

# =============================================================================
# Complexity analysis (question 4)
#
# First we will look at the complexity if we had a 1 letter word. 
# We have to explore the graph of e-links which has m+1 vertices and since each
# vertex has at most 4 neighbours, the graph has O(m) edges. 
# Thus the complexity of the exploration is O(m) which means the overall complexity
# of the algorith is O(m) (the only thing that affects running time is the exploration)
# =============================================================================
  



 
