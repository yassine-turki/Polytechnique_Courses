# -*- coding: utf-8 -*-

# the input is represented by a list of (left,height,right)
# the output (skyline) is represented by an ordered list of (left,height) and always ends with 
# a (left,0) entry

def rects_height_at(rects, x):
    """
    given a list of rectangles and a position, return h(x)=max{h:(l,h,r) in rects and l<=x<r}
    note that the inequality l<=x<r is assymetric: large on the left and strict on the right
    """
    return max([0] + [h for (left,h,right) in rects if left <= x and x < right])

def simplify_skyline(skyline):
    """simplify a skyline by removing redundant entries"""
    out_sky = []
    cur_h = 0
    for (x,h) in skyline:
        # if the next entry has the same height as the previous one, discard it
        if h != cur_h:
            out_sky.append((x,h))
        cur_h = h
    return out_sky

def skyline_naive(rects):
    """computes the skyline in O(n^2)"""
    # let P be the set of x-coordinates that appear in rects:
    # P={l:(l,r,y) in rects} union {r:(l,r,y) in rects}
    # then if we sort P, the skyline can be defined as
    # [(x,h(x)) for x in sorted(P)]
    # remark: we go through a set to make the elements unique
    coords = sorted(list(set([left for (left,_,_) in rects] + [right for (_,_,right) in rects])))
    return simplify_skyline([(x,rects_height_at(rects, x)) for x in coords])

def merge_skylines(sky1, sky2):
    """merge two skylines"""
    out_sky = []
    h1 = h2 = 0
    while len(sky1) > 0 and len(sky2) > 0:
        (x1,nexth1) = sky1[0]
        (x2,nexth2) = sky2[0]
        # pick the first
        if x1 < x2:
            h1 = nexth1
            out_sky.append((x1, max(h1, h2)))
            sky1 = sky1[1:]
        elif x1 > x2:
            h2 = nexth2
            out_sky.append((x2, max(h1, h2)))
            sky2 = sky2[1:]
        else: # same position
            h1 = nexth1
            h2 = nexth2
            out_sky.append((x1, max(h1, h2)))
            sky1 = sky1[1:]
            sky2 = sky2[1:]
    # add what remains
    out_sky += sky1
    out_sky += sky2
    return simplify_skyline(out_sky)

def skyline_dac(rects):
    if len(rects) == 1:
        (left,h,right) = rects[0]
        return [(left,h),(right,0)]
    # divide and conquer
    n = len(rects) // 2
    sky1 = skyline_dac(rects[0:n])
    sky2 = skyline_dac(rects[n:])
    return merge_skylines(sky1, sky2)
