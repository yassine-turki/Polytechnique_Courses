# -*- coding: utf-8 -*-

# the input is represented by a list of (left,height,right)
# the output (skyline) is represented by an ordered list of (left,height) and always ends with
# a (left,0) entry

def rects_height_at(rects, x):
    """
    given a list of rectangles and a position, return h(x)=max{y:(l,r,y) in rects and l<=x<r}
    note that the inequality l<=x<r is assymetric: large on the left and strict on the right
    """
    Max = 0
    for i in range(len(rects)):
        l = rects[i][0]
        r = rects[i][2]
        h = rects[i][1]
        if x >= l and x < r and Max < h:
            Max = h
    return Max


def simplify_skyline(skyline):
    """simplify a skyline by removing redundant entries"""
    l = [skyline[0]]
    for i in range(len(skyline)-1):
        if skyline[i][1] != skyline[i+1][1]:
            l.append(skyline[i+1])
    return l


def skyline_naive(rects):
    """computes the skyline in O(n^2)"""
    coords = sorted(
        list(set([left for (left, _, _) in rects]+[right for (_, _, right) in rects])))
    return simplify_skyline([(x, rects_height_at(rects, x)) for x in coords])


def merge_skylines(sky1, sky2):
    """merge two skylines"""
    nsky1 = []
    for i in range(len(sky1)-1):
        k = 0
        while sky1[i][0]+k < sky1[i+1][0]:
            nsky1.append((sky1[i][0]+k, sky1[i][1]))
            k += 1
    last1 = nsky1[-1][0]
    x = 1
    while last1+x <= sky1[-1][0]:
        nsky1.append((last1+x, sky1[-1][1]))
        x += 1
    nsky2 = []
    for i in range(len(sky2)-1):
        k = 0
        while sky2[i][0]+k < sky2[i+1][0]:
            nsky2.append((sky2[i][0]+k, sky2[i][1]))
            k += 1
    last2 = nsky2[-1][0]
    x = 1
    while last2+x <= sky2[-1][0]:
        nsky2.append((last2+x, sky2[-1][1]))
        x += 1
    res=[]
    for i in range(min(len(nsky1), len(nsky2))):
        if nsky1[i][0] == nsky2[i][0]:
            continue
        if  nsky1[i][0]< nsky2[i][0]:
            res.append((nsky2[i][0],max(nsky1[i][1],nsky2[i][1])))
    return res


def skyline_dac(rects):
    pass
