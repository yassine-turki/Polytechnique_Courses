#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import numpy as np
import random
import math

# #Q1
# def min_max_aux(A, left, right):
#     if left==right-1:
#         return (A[left],A[left])
#     k=(left+right)//2
#     min1,max1=min_max_aux(A, left, k)
#     min2,max2=min_max_aux(A, k, right)
#     return (min(min1,min2),max(max1,max2))
    
#     # if left == right-1:
#     #     return (A[left], A[left])
#     # k = (left + right)//2
#     # min1, max1 = min_max_aux(A, left, k)
#     # min2, max2 = min_max_aux(A, k, right)
#     # return ( min(min1, min2) , max(max1, max2) )

# def min_max(A):# This function returns both the minimum and the maximum of A
#     # if len(A)==1:
#     #     return (min(A),max(A))
#     # mid=len(A)//2
#     # return (min(min_max(A[:mid])+min_max(A[mid:])),max(min_max(A[:mid])+min_max(A[mid:])))
    
#     return min_max_aux(A, 0, len(A))

#     #Recurrence relation : T(n)=2*T(n/2)+2
#     #Values for first terms:

# #Recurrence relation: T(n) = 2T(n/2) + 2
# #Values for the first terms:
# #    n = 1: T(n) = 0
# #    n = 2: T(n) = 2*0+2 = 2

# #Q2
# # This function returns the coordinates of both the top-left and bottom-right corners.
# def bounding_box(S):
#     x=[]
#     y=[]
#     for i in range(len(S)):
#         x.append(S[i][0])
#         y.append(S[i][1])
    
#     minx,maxx=min_max(x)  
#     miny,maxy=min_max(y) 
#     return [[minx,maxy],[maxx,miny]]
    
    
    
#     # xi = [ x[0] for x in S]
#     # yi = [ x[1] for x in S]
#     # a1, b1 = min_max(xi)
#     # b2, a2 = min_max(yi)
#     # return [[a1, a2],[b1,b2]]

# #Q3
# def maxima_set(S):
#     n=len(S)
#     if n<=1:
#         return S
#     p=len(S)//2
#     solve1=maxima_set(S[:p])
#     solve2=maxima_set(S[p:])
#     q=solve2[0]
#     newsolve=[]
#     for element in solve2:
#         if lexicographic(element, q):
#             q=element
#     for element in solve1:
#         if q[0]<=element[0] and q[1]<=element[1]:
#                 solve1.remove(element)
#     res=solve1+solve2
#     return res
               
#     #Recurrence relation: T(n)= 2T(n/2)+2*(n/2)
    
#     # n = len(S)
#     # if n <= 1:
#     #     return S
    
#     # k = n//2
#     # S1 = maxima_set(S[:k])
#     # S2 = maxima_set(S[k:])
#     # q = S2[0]
#     # # for element in S2:
#     # #     if lexicographic(element, q):
#     # #         q = element
    
#     # for element in S1:
#     #     if element[0] <= q[0] and element[1] <= q[1]:
#     #         S1.remove(element)
    
#     # return S1 + S2

# #Recurrence relation: T(n) = 2T(n/2) + 2*(n/2) = 2T(n/2) + n


# #Q4

def dominated(C, left, right, b):
    if left == right - 1:
        if b >= C[0][1]:
            return 1
        else:
            return 0
    k = (left+right)//2
    if b >= C[k][1]:
        return k + dominated(C, k, right, b)
    else:
        return dominated(C, left, k, b)
    
# # def my_y_coordinate(A):
#     pass
# #     return A[1]

# def dominance_counting(S):
#     n=len(S)
#     if n==0:
#         return []
#     if n==1:
#         return [S[0],0]
#     p=n//2
#     solve1=dominance_counting(S[:p])
#     solve2=dominance_counting(S[p:])
#     return S
    
    
    
    
    
    
# #     n = len(S)
# #     if n == 0:
# #         return []
# #     if n == 1:
# #         return [[S[0], 0]]
    
# #     k = n//2
# #     S1 = dominance_counting(S[:k])
# #     S2 = dominance_counting(S[k:])
    
# #     C = S[:k]
# #     C.sort(key=my_y_coordinate)
# #     R = []
# #     for q in S2:
# #         x, c = q
# #         a, b = x
# #         R += [ [x, c + dominated(C, 0, len(C), b)] ]
# #     return S1 + R
        
    
    

# # Auxilliary functions

def lexicographic(p1,p2):
    if (p1[0] < p2[0]):
        return True
    elif (p1[0] == p2[0] ):
        return p1[1] <= p2[1]
    return False

def y_coordinate(A):
    return A[1]
    
def sort_y(C):
    C.sort(key=y_coordinate)
    
def min_max_aux(A,left,right):
    if left==right-1:
        return (A[left],A[left])
    mid=(left+right)//2
    min1,max1=min_max_aux(A,left,mid)
    min2,max2=min_max_aux(A,mid,right)
    return (min(min1,min2),max(max1,max2))

def min_max(A):
    return min_max_aux(A, 0, len(A))

def bounding_box(S):
    x=[]
    y=[]
    for element in S:
        x.append(element[0])
        y.append(element[1])
    minx,maxx=min_max(x)
    miny,maxy=min_max(y)
    return [[minx,maxy],[maxx,miny]]

def maxima_set(S):
    n=len(S)
    if n<=1:
        return S
    p=n//2
    left=maxima_set(S[:p])
    right=maxima_set(S[p:])
    q=right[0]
    for element in right:
        if lexicographic(element, q):
            q=element
    for element in left:
        if q[0]>=element[0] and q[1]>=element[1]:
            left.remove(element)
    return left+right

#Complexity: T(n)= 2*T(n/2)+2*(n/2)=2T(n/2)+n

def dominance_counting(A):
    n=len(A)
    if n==0:
        return []
    if n==1:
        return [[A[0],0]]
    p=n//2
    left=dominance_counting(A[:p])
    right=dominance_counting(A[p:])
    l=A[:p]
    l.sort(key=y_coordinate)
    for r in right:
        index=binary_search_rec(l,r[0][1], 0, len(right)-1)
        r[1]=len(l)-index
    return left+right
                
    
def binary_search_rec(A,v,left,right):
    mid = left + (right - left)//2
    if (right >= left):
         # using `(right + left)//2` can lead to an integer overflow
        if (v == A[mid][1]):
            return mid
        elif (v < A[mid][1]):
            return binary_search_rec(A,v,left,mid-1)
        else:
            return binary_search_rec(A,v,mid+1,right)
    for i in range(10**9):
        if mid+i==v:
            return mid+i
        if mid-i==v:
            return mid-i
        


            





