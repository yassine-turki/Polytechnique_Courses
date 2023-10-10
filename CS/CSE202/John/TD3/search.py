# -*- coding: utf-8 -*-

import math

def binary_search_rec(A,v,left,right):
    if (right >= left):
        mid = left + (right-left)//2
        if (v == A[mid]):
            return mid
        elif (v < A[mid]):
            return binary_search_rec(A,v,left,mid-1)
        elif (v > A[mid]):
            return binary_search_rec(A,v,mid+1,right)
    else:
        return -1
        
## Q1 ##
def binary_search(A,v):
    n = len(A)
    left = 0
    right = n-1 
    while left <= right:
        m = (left + right) //2
        
        if A[m] < v:
            left = m+1
        elif A[m] > v:
            right = m-1
        else:
            return m 
    return -1 

## Q1 ##
def cost_binary_search(n):
    if n ==1 or n == 0: 
        return 1
    else:
        return cost_binary_search(math.ceil(n/2)) + 2 
    
    
## Q2 ##
def ternary_search(A,v):
    n = len(A)
    left = 0
    right = n-1
    while left <= right: 
        m1 = left + (right -left) // 3
        m2 = right - (right - left )// 3
        
        if v == A[m1]:
            return m1
        if v == A[m2]:
            return m2
        
        if v < A[m1]:
            right = m1 -1
        elif v > A[m2]:
            left = m2 + 1
        else:
            left = m1 + 1
            right = m2 -1
    return -1 

## Q2 ##
def cost_ternary_search(n):
    if  n == 0:
        return 1 
    else:
        return cost_ternary_search(math.ceil(n/3)) + 4 
    
# =============================================================================
#  We can see that ternary search makes 4 comparisons at each iteration instead
#  of two for binary search. 
#  Mathematically, we can also deduce that since the complexity of ternary search 
#  is 2*log3(2) times the one of binary search, and since 2*log3(2) > 1. It makes sense 
#  that binary search is actually better than ternary search.    
# =============================================================================
    
    
## Q3 ##
def exponential_search(A,v):
    i = 1
    n = len(A)
    while i < n and A[i] <= v:
        i = i*2
        
    return binary_search_rec(A, v, i//2,  min(i, n-1))

## Q3 ##
def cost_exponential_search(n):
    if n == 1 or n == 0:
        return 1
    return cost_binary_search(math.ceil(n/2)) + math.log(2,n)

## Q4 ##
def interpolation_search(A,v):
    n = len(A)
    left = 0
    right = n -1 
    
    while A[right] != A[left] and A[left] <= v <= A[right]:
        k = left + (v - A[left]) * (right - left) // (A[right] - A[left])
        if v == A[k]:
            return k
        elif v < A[k]:
            right = k-1
        else:
            left = k+1 
    
    if v == A[left]:
        return left
    
    return -1
    

## Q6 ##
def findFirstOccurrence(A, v):
    n = len(A)
    left = 0
    right = n 
    while left != right:
        m = left + (right - left)//2
        if v == A[m] and left + 1 ==right:
            return m
        if m+1 < n:
            if v == A[m+1] and left+1 == right:
                return m +1
        if v == A[m]:
            right = m 
        elif v < A[m]:
            right = m
        else:
            left = m
    return -1 

    
## Q6 ##
def findLastOccurrence(A, v):
    n = len(A)
    left = 0
    right = n 
    while left != right:
        m = left + (right - left)//2
        if v == A[m] and left + 1 ==right:
            return m
        
        if v == A[m]:
            left = m 
        elif v < A[m]:
            right = m
        else:
            left = m
    return -1 


## Q7 ##
def findKClosestElements(A, v, k):
    b = []
    if v < A[0]:
        n = 0          
    elif v > A[-1]:
        n = len(A) - k
        
    else:
        p= 0
        t = v
        for i in range(k):
            while binary_search(A,v) == -1:
                p +=1
                if p%2 ==1:
                    v+1
                else:
                    v-=1 
                    
            n = binary_search(A,v) - k//2
            
            while n < 0:
                n+=1   
                
    while v-A[n-1] < A[n+k-1]-v and n-1 >= 0:
        n = n-1
        
    while n + k < len(A)-1 and v - A[n] > A[n+k]- v:
        n =n+1
               
    for i in range(n , n+k):
        b.append(A[i])
    
        
    return b
## Q8 ##
def findFrequency(A):
    d = {}
    i = 0
    while i < len(A):
        v = A[i]
        k = findLastOccurrence(A, v)
        d[v] = (k+1)-i
        i = k+1
    return d 
    
def findKthSmallestElement(A, B,k): 
        iMin = 0
        iMax = k-1 

        while (iMin <= iMax):
            i = (iMin + iMax) // 2;
            j = k - 1 - i
            if (B[j - 1] > A[i]) :
                iMin = i + 1;
            elif i > 0 and A[i - 1] > B[j] :
                iMax = i - 1;
            else :
               return min(A[i], B[j])

        return -1;
        








