from random import randint, uniform

## Question 7
# Return a bit string of length n uniformly at random from {0, 1}^n.
def createBitStringUniformly(n):
    l=[]
    res=[]
    for i in range(n):
        l.append(randint(0,1))
    return l


## Question 8
# Return a new bit string that performed single-bit flip mutation on a copy of x.
def singleBitFlip(x):
    l=x.copy()
    rand=randint(0,len(l)-1)
    l[rand]=1-l[rand]
    return l

## Question 9
# Return a new bit string that performed standard bit mutation on a copy of x.
# Expected number of different bits between x and the mutant: 
def standardBitMutation(x):
    l=x.copy()
    for i in range(len(l)):
        if randint(0,len(l))==0:
            l[i]=1-l[i]
    return l


## Question 10
# Return a tuple (x, it), where x is the best solution found and it is the number of iterations.
def rsh(n, f, terminated, mutation):
    pass


## Question 11
# (1 + 1) EA on OneMax (on n bits)
#    Pr[A_i] ≥ 
#    Expected run time is at most: 
#
# RLS on LeadingOnes (on n bits)
#    Pr[A_i] = 
#    Expected run time is at most: 