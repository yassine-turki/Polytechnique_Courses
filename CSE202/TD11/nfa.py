from dg import *

# Question 5
def contains_pattern(s, text):
  pass

class NFA:
    def __init__(self, s): # s is the string containing the regular expression
        self.s = s
        self.m = len(self.s)
        self.dg = DG(len(s) + 1) # the directed graph that stores the epsilon links
        self.lp = [-1 for _ in range(len(s))]
        self.rp = [-1 for _ in range(len(s))]
        self.left_right_match_or() # assigns lp and rp according to parentheses matches
        self.build_eps_links() # assigns the epsilon links in self.dg

    def __str__(self):
        n = self.m
        str_lp = 'lp: '
        str_rp = 'rp: '
        for i in range(self.m):
            if self.lp[i] == -1:
                str_lp += '-1  '
            elif self.lp[i] < 10:
                str_lp += str(self.lp[i]) + '   '
            else: str_lp += str(self.lp[i]) + '  '
            if self.rp[i] == -1:
                str_rp += '-1  '
            elif self.rp[i] < 10:
                str_rp += str(self.rp[i]) + '   '
            else: str_rp += str(self.rp[i]) + '  '
        str_lp += '\n'
        str_rp += '\n'

        str_dg = str(self.dg)

        s = '------------------\nRegular expression\n------------------\n' + 're: ' + '   '.join(self.s) + '\n'
        return s + str_lp + str_rp #+ '------------------\nCorresponding NFA\n------------------\n' + str_dg

    ## Question 1
    def left_right_match(self):
        pass

    ## Question 2
    def left_right_match_or(self):
        pass

    ## Question 3
    def build_eps_links(self):
        pass

    ## Question 4
    # Complexity: 
    # Because: 
    def check_text(self, w):
        pass
