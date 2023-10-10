# -*- coding: utf-8 -*-
"""
Given a histogram, find the largest area of a rectangle contained in the
histogram.
"""
import math
import random

def random_hist(n):
    """generate a random instance"""
    return [random.randint(1, n) for _ in range(n)]

# for reference: what NOT to do: O(n^2)
def rect_from_left_bad(hist, i):
    """compute max area of a rectangle [i,j] for all j, in QUADRATIC time"""
    max_area = 0
    for j in range(i, len(hist)):
        max_area = max(max_area, (j - i + 1) * min(hist[i:j+1]))
    return max_area

# for reference: what NOT to do: O(n^2)
def rect_from_left(hist, i):
    """compute max area of a rectangle [i,j] for all j, in linear time"""
    # now increase rectangle to the right, keep track of the small height
    # we have seen since the beginning
    min_h = math.inf
    max_area = 0
    for j in range(i, len(hist)):
        min_h = min(min_h, hist[j])
        max_area = max(max_area, (j - i + 1) * min_h)
    return max_area

def rect_hist_brute(hist):
    """brute force (n^2) solution"""
    max_area = hist[0]
    # start rectangle at position i
    for i in range(len(hist)):
        max_area = max(max_area, rect_from_left(hist, i))
    return max_area

# for reference of what NOT to do
def expand_rect_bad(hist, i, j, left, right, h):
    """expand rectangle [l:r] to the left or the right, update height"""
    # if left is at the boundary, expand right, and symmetrically
    if i == left:
        right += 1
    elif right == j:
        left -= 1
    else:
        # otherwise, expand in the directory of the highest
        if hist[left - 1] > hist[right]:
            left -= 1
        else:
            right += 1
    return left, right, min(hist[left:right])

def expand_rect(hist, i, j, left, right, h):
    """expand rectangle [l:r] to the left or the right, update height"""
    # if left is at the boundary, expand right, and symmetrically
    if i == left:
        right += 1
    elif right == j:
        left -= 1
    else:
        # otherwise, expand in the directory of the highest
        if hist[left - 1] > hist[right]:
            left -= 1
        else:
            right += 1
    return left, right, min(h, hist[left], hist[right-1])

def best_from_middle(hist, i, j, m):
    """compute max area of a rectangle that includes bar at position m"""
    left,right,h = m,m+1,hist[m] # cur height and window
    max_area = h # best area so far
    # increase the interval [left,right] until we reach [i,j]
    while i < left or right < j:
        left, right, h = expand_rect(hist, i, j, left, right, h)
        max_area = max(max_area, (right - left) * h)
    return max_area

def rect_hist_dac_aux(hist, i, j):
    """solve over interval [i,j)"""
    if i == j:
        return -math.inf
    m = (i + j) // 2
    # recursve on the left and right (both exclude the middle bar m)
    # NOTE clearly i < j thus i <= m so first interval makes sense
    # and similarly i + j < 2 * j thus m < j thus m+1 <= j
    max_area = max(rect_hist_dac_aux(hist, i, m),
                   rect_hist_dac_aux(hist, m + 1, j))
    return max(max_area, best_from_middle(hist, i, j, m))

def rect_hist_dac(hist):
    """divide-and-conquer (nlog(n)) solution"""
    return rect_hist_dac_aux(hist, 0, len(hist))
