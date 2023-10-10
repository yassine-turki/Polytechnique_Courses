def binom(n,k):
    if k==0:
        return 1
    if k>n:
        return 0
    else:
        return binom(n-1,k)+binom(n-1,k-1)

def choose(s,k):
    if k==0:
        return [[0]]
    if k>len(s):
        return [[s]]
    else:
        return choose(s[:len(s)-1],k)+choose(s[:len(s)-1],k-1)
    
def factorial(n):
    if n == 0:
        return 1
    return n * factorial(n-1)

def permutations(l):
    if factorial(len(l))==1:
        return [l]
    if factorial(len(l))==2:
        return [[l[0],l[1]]]+[[l[1],l[0]]]
    else:
        for i in range(len(l)):
            return permutations(l[:i])+[l[0]]+permutations(l[1:])


def not_angry(n):
    if n==0:
        return 1
    if n==1:
        return 2
    if n==2:
        return 3
    return not_angry(n-1)+not_angry(n-2)
       