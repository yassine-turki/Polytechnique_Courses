# -*- coding: utf-8 -*-
"""
Given a histogram, find the largest area of a rectangle contained in the
histogram.
"""
import math

# def rect_from_left(hist, i):
#     """compute max area of a rectangle [i,j] for all j, in linear time"""
#     Max=0
#     c=0
#     Min=10**9
#     for t in range(len(hist)-i):
#         if hist[t+i]<Min:
#             Min=hist[t+i]
#         c=Min*(t+1)
#         if c>Max:
#             Max=c
#     return Max
        
    


# def rect_hist_brute(hist):
#     """brute force (n^2) solution"""
#     Max=0
#     for i in range(len(hist)):
#         rect=rect_from_left(hist, i)
#         if Max<rect:
#             Max=rect
#     return Max

# def expand_rect(hist, i, j, left, right, h):
#     """expand rectangle [l:r] to the left or the right, update height"""
#     rp=right
#     lp=left
#     hp=h
#     if lp==i:
#         hp=min(hp,hist[rp])
#         rp=rp+1
        
#     elif rp==j:
#         lp=lp-1
#         hp=min(hp,hist[lp])
#     elif hist[lp-1]>hist[rp]:
#         lp=lp-1
#         hp=min(hp,hist[lp])
#     else:
#         hp=min(hp,hist[rp])
#         rp=rp+1
        
#     return (lp,rp,hp)

# def best_from_middle(hist, i, j, m):
#     """compute max area of a rectangle that includes bar at position m"""
#     l=m
#     r=m+1
#     h=hist[m]
#     area=h
#     while l>i or r<j:
#         x=expand_rect(hist, i, j, l, r, h)
#         l,r,h=x
#         area=max(area,(r-l)*h)
#     return area

# def rect_hist_dac_aux(hist, i, j):
#     """solve over interval [i,j)"""
#     m=(i+j)//2
#     if i==j:
#         return -math.inf
#     else:
#         area=max(rect_hist_dac_aux(hist, i, m),rect_hist_dac_aux(hist, m+1, j))
#         return max(area,best_from_middle(hist, i, j, m))

# def rect_hist_dac(hist):
#     """divide-and-conquer (nlog(n)) solution"""
#     return rect_hist_dac_aux(hist, 0, len(hist))

def rect_from_left(hist, i):
    count=1
    s={}
    for t in range(i,len(hist)):
        if hist[i]>hist[t]:
            s.add(hist[t]*count)
        else:
            s.add(hist[i]*count)
        count+=1
    return max(s)
        