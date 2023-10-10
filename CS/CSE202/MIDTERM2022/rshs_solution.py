from random import randint, uniform

## Question 7
# Return a bit string of length n uniformly at random from {0, 1}^n.
def createBitStringUniformly(n):
    x = list()
    for _ in range(n):
        bit = 0
        if uniform(0, 1) < 0.5:
            bit = 1
        x.append(bit)
    return x


## Question 8
# Return a new bit string that performed single-bit flip mutation on a copy of x.
def singleBitFlip(x):
    y = x.copy()
    i = randint(0, len(x) - 1)
    y[i] = 1 - y[i]
    return y


## Question 9
# Return a new bit string that performed standard bit mutation on a copy of x.
# Expected number of different bits between x and the mutant: 1
def standardBitMutation(x):
    y = x.copy()
    n = len(y)
    p = 1 / n
    for i in range(n):
        if uniform(0, 1) <= p:
            y[i] = 1 - y[i]
    return y


## Question 10
# Return a tuple (x, it), where x is the best solution found and it is the number of iterations.
def rsh(n, f, terminated, mutation):
    x = createBitStringUniformly(n)
    it = 0
    while not terminated(x, it):
        y = mutation(x)
        if f(y) >= f(x):
            x = y
        it += 1
    return (x, it)


## Question 11
# (1 + 1) EA on OneMax (on n bits)
#    Pr[A_i] ≥ (n − i)/(en)
#    Expected run time is at most: O(n log(n))
#
# RLS on LeadingOnes (on n bits)
#    Pr[A_i] = 1/n
#    Expected run time is at most: O(n²)