# -*- coding: utf-8 -*-

import math

def binary_search_rec(A,v,left,right):
    if (right >= left):
        mid = left + (right - left)//2 # using `(right + left)//2` can lead to an integer overflow
        if (v == A[mid]):
            return mid
        elif (v < A[mid]):
            return binary_search_rec(A,v,left,mid-1)
        else:
            return binary_search_rec(A,v,mid+1,right)
    
    return -1
        
## Q1 ##
def binary_search(A,v,lower=-1,upper=-1):
    n=len(A)
    if lower==-1:
        lower=0
        upper=n-1
    while lower<=upper:
        mid = lower + (upper - lower) // 2
        if A[mid]==v:
            return mid
        elif A[mid]<v:
            lower=mid+1
        elif A[mid]>v:
            upper=mid-1
    return -1

def cost_binary_search(n):
    if n==0:
        return 1
    if n==1:
        return 3
    return cost_binary_search(math.ceil(n/2))+3
    
## Q2 ##
def ternary_search(A,v):
    n=len(A)
    l=0
    r=n-1
    while l<=r:
        part1 = l + ((r -l) // 3)
        part2 = r - ((r - l)// 3)
        if v == A[part1]:
            return part1
        if v == A[part2]:
            return part2
        if v < A[part1]:
            r = part1 -1
        elif v > A[part2]:
            l = part2 + 1
        else:
            l = part1 + 1
            r = part2 -1
    return -1 

def cost_ternary_search(n):
    if  n == 0:
        return 1
    if n==1:
        return 4
    else:
        return cost_ternary_search(math.ceil(n/3)) + 4 
    
def cost_binary_search_real(A,v):
    if len(A) == 0: return 0

    left = 0
    right = len(A) - 1
    cost =  0
    while (right >= left):
        cost += 1
        mid = left + (right - left)//2
        if (v == A[mid]):
            return cost + 1
        elif (v < A[mid]):
            right = mid - 1
            cost += 2
        else:
            left = mid + 1
            cost += 2

    return cost

def cost_ternary_search_real(A,v):
    if len(A)==0: return 0
    n=len(A)
    l=0
    r=n-1
    cost=0
    while l<=r:
        part1 = l + ((r -l) // 3)
        part2 = r - ((r - l)// 3)
        if v == A[part1]:
            return cost+1
        if v == A[part2]:
            cost+=2
            return cost +2
        if v < A[part1]:
            r = part1 -1
            cost+=3
        elif v > A[part2]:
            l = part2 + 1
            cost+=4
        else:
            l = part1 + 1
            r = part2 -1
            cost+=4
    return cost


## Q3 ##
def exponential_search(A,v):
    k=0
    while 2**k<len(A) and A[2**k]<=v :
        k+=1
    l=2**(k-1)
    r=2**k
    return binary_search(A, v,int(l),min(int(r),len(A)))

def cost_exponential_search(n):
    if n == 0 or n == 1:
        return 1
    return cost_binary_search(math.ceil(n/2)) + math.log(2,n)

## Q4 ##
def interpolation_search(A,v):
    n = len(A)
    l = 0
    r = n -1 
    while A[r] != A[l] and A[l] <= v <= A[r]:
        k = l + (v - A[l]) * ((r - l) // (A[r] - A[l]))
        if v == A[k]:
            return k
        elif v < A[k]:
            r = k-1
        else:
            l = k+1 
    
    if v == A[l]:
        return l
    return -1

## Q6 ##
def findFirstOccurrence(A, v):
    if binary_search(A, v)==-1: return -1
    n=len(A)
    lower=0
    upper=n
    while lower<=upper:
        mid = lower + (upper - lower) // 2
        if A[mid]==v and lower + 1 ==upper:
            return mid
        if A[mid+1]==v and lower+1 == upper and mid+1<n:
            return mid +1
        if A[mid]>=v:
            upper=mid
        else:
            lower=mid

def findLastOccurrence(A, v):
    if binary_search(A, v)==-1: return -1
    n=len(A)
    lower=0
    upper=n
    while lower<=upper:
        mid = lower + (upper - lower) // 2
        if A[mid]==v and lower + 1 ==upper:
            return mid
        if A[mid]<=v:
            lower=mid
        else:
            upper=mid

## Q7 ##
def findKClosestElements(A, v, k):
    if v<A[0]:
        return [A[i] for i in range(0,k)]
    if v>A[-1]:
        return [A[i] for i in range(len(A)-k,len(A))]
    else:
        l=[]
        search=binary_search(A, v)
        if search !=-1:
                n=int(k/2)
                for i in range(n,0,-1):
                    l.append(A[search-i])
                for i in range(n+1):
                    l.append(A[search+i])
        else:
            var=0
            while binary_search(A, v)==-1:
                var+=1
                if var%2==0:
                    v-=1
                else:
                    v+=1
            if k%2==0:
                n=int(k/2)
            else:
                n=int((k+1)/2)
            search=binary_search(A, v)
            for i in range(n,0,-1):
                if search-i>=0:
                    l.append(A[search-i])
            for i in range(n):
                if search+i<len(A):
                    l.append(A[search+i])
        return l
    

## Q8 ##
def findFrequency(A):
    d= {}
    i = 0
    while i < len(A):
        v = A[i]
        k = findLastOccurrence(A, v)
        d[v] = k+1-i
        i = k+1
    return d 
