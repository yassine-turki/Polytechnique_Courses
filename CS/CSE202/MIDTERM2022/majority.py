from math import log, log2
from random import randint

## Question 1
# Return frequency of v in L[start:stop].
# The worst-case run time is:  O(n)
# Because: If start=0 and n, and v is not in L, the for loop will iterate n times. 
def getFrequency(v, L, start, stop):
    n=len(L)
    count=0
    for i in range(start,stop):
        if L[i]==v:
            count+=1
    return count
        
        


## Question 2
# Return majority element of L if it exists, otherwise 'False'.
# The worst-case run time is: O(n^2)
# Because: for the worst case, we execute n times the function getFrequency of complexity O(n). Hence, the complexity is O(n*n)=O(n^2)
def getMajorityNaively(L):
    n=len(L)
    res=[]
    for v in L:
        res.append(getFrequency(v, L, 0, n))
    for i in range(len(res)):
        if res[i]>n//2:
            return L[i]
    return False


## Question 3
# Return majority element of L if it exists, otherwise 'False'.
# The worst-case run time is: O(n log(n))
# Because: Recurrence: T(n)=2T(n/2)+O(n) (Master Theorem)
def getMajorityDaC(L):
    n=len(L)
    def helpGetMajorityDaC(start, stop):
        if start==stop-1 :
            return L[start]
        k=start + (stop - start)//2
        a=helpGetMajorityDaC(start, k)
        b=helpGetMajorityDaC(k, stop)
        if getFrequency(a, L, 0, n)>=getFrequency(b, L, 0, n):
            return a
        else:
            return b
    element= helpGetMajorityDaC(0, n)
    if getFrequency(element, L, 0, n)>n//2:
        return element
    else:
        return False


## Question 4
# Return majority element of M if it exists, otherwise 'False'.
# The worst-case run time is: O(n^2)
# Because: 
def getMajorityInMatrixDaC(M):
    n=len(M)
    def helpGetMajorityDaC(rowStart, rowStop, colStart, colStop):
        a=helpGetMajorityDaC(rowStart, rowStop)
        b=helpGetMajorityDaC(colStart, colStop)
        return max(a,b)
    element= helpGetMajorityDaC(0, n,0,n)
    if getFrequency(element, M, 0, n)>n//2:
        return element
    else:
        return False

# Returns the frequency of v in M[rowStart:rowStop][colStart:colStop].
def getFrequencyFromMatrix(v, M, rowStart, rowStop, colStart, colStop):
    freq = 0
    for row in range(rowStart, rowStop):
        freq += getFrequency(v, M[row], colStart, colStop)
    return freq


## Question 5
# Return majority element of L if it exists, otherwise 'False'.
# The worst-case run time is: O(n)
# Because: We iterate over the list of length n and we use the function getFrequency of complexity O(n)
def getMajorityBoyerMoore(L):
    freq=0
    curr=None
    n=len(L)
    for element in L:
        if freq==0:
            curr=element
            freq+=1
        else:
            if curr!=element:
                freq-=1
    if getFrequency(curr, L, 0, n)>n//2:
        return curr
    else:
        return False
            


## Question 6
# Return majority element of L with probability at least p if it exists, otherwise 'False'.
# Probability for one try finding the existing majority element is at least: n/2 (By definition)
# Probability that m tries all fail (assuming a majority element exists) is at most:  p of getting False is 1-p< 1-n/2. Hence, after m tries, the probability is at most (1-(n/2))^m 
def getMajorityRandomized(L, p):
    n=len(L)
    while True:
        idx=randint(0,n-1)
        if idx<=p:
            if getFrequency(L[idx], L, 0, n)>n//2:
                return idx
            else:
                return False
    
    
    