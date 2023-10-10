# -*- coding: utf-8 -*-

import numpy as np
from points import *

grading_mode = False

def test_min_max():
    A1 = [3,12,10,2,0,4]
    A2 = [2,1,10,2,12,4,3]
    if min_max(A1) is None:
        print("***** skipping min_max (unimplemented)")
        assert not grading_mode
        return
    r1,r2 = min_max(A1)
    if (not ((r1 == 0 and r2 == 12) or (r1 == 12 and r2 == 0))):
        print("***** min_max\n your result\n {}\n is wrong for the array\n {}\n*****".format([r1,r2],A1))
    r1,r2 = min_max(A2)
    if (not ((r1 == 1 and r2 == 12) or (r1 == 12 and r2 == 1))):
        print("***** min_max\n your result\n {}\n is wrong for the array\n {}\n*****".format([r1,r2],A2))

def test_bounding_box():
    S1 = [[2,6],[3,7],[4,6],[6,4],[8,5]]
    S2 = [[2,6],[3,7],[4,5],[6,4],[8,6],[9,3],[10,2],[11,2]]
    if bounding_box(S1) is None:
        print("***** skipping bounding_box (unimplemented)")
        assert not grading_mode
        return
    R = bounding_box(S1)
    if (not (((R[0][0] == 2 and R[0][1] == 7) and (R[1][0] == 8 and R[1][1] == 4)) or ((R[0][0] == 8 and R[0][1] == 4) and (R[1][0] == 2 and R[1][1] == 7)))):
        print("***** bounding_box\n your result\n {}\n is wrong for the set\n {}\n*****".format(R,S1))
    R = bounding_box(S2)
    if (not (((R[0][0] == 2 and R[0][1] == 7) and (R[1][0] == 11 and R[1][1] == 2)) or ((R[0][0] == 11 and R[0][1] == 2) and (R[1][0] == 2 and R[1][1] == 7)))):
        print("***** bounding_box\n your result\n {}\n is wrong for the set\n {}\n*****".format(R,S2))
        
def test_maxima_set():
    S1 = [[2,6],[3,7],[4,6],[6,4],[8,5]]
    S2 = [[2,6],[3,7],[4,5],[6,4],[8,6],[9,3],[10,2],[11,2]]
    if maxima_set(S1) is None:
        print("***** skipping maxima_set (unimplemented)")
        assert not grading_mode
        return
    R = maxima_set(S1)
    if ([3,7] not in R) or ([4,6] not in R) or ([8,5] not in R):
        print("***** maxima_set\n your result\n {}\n is wrong for the set\n {}\n*****".format(R,S1))
    R = maxima_set(S2)
    if ([3,7] not in R) or ([9,3] not in R) or ([8,6] not in R) or ([9,3] not in R) or ([11,2] not in R):
        print("***** maxima_set\n your result\n {}\n is wrong for the set\n {}\n*****".format(R,S2))
        
def test_dominance_counting():
    S1 = [[2,6],[3,7],[4,6],[6,4],[8,5]]
    S2 = [[2,6],[3,7],[4,5],[6,4],[8,6],[9,3],[10,2],[11,2]]
    if dominance_counting(S1) is None:
        print("***** skipping dominance_counting (unimplemented)")
        assert not grading_mode
        return
    R = dominance_counting(S1)
    if ([[2,6],0] not in R) or ([[3,7],1] not in R) or ([[4,6],1] not in R) or ([[6,4],0] not in R) or ([[8,5],1] not in R):
        print("***** dominance_counting\n your result\n {}\n is wrong for the set\n {}\n*****".format(R,S1))
    R = dominance_counting(S2)
    if ([[2,6],0] not in R) or ([[3,7],1] not in R) or ([[4,5],0] not in R) or ([[6,4],0] not in R) or ([[9,3],0] not in R) or ([[8,6],3] not in R) or ([[9,3],0] not in R) or ([[10,2],0] not in R) or ([[11,2],1] not in R):
        print("***** dominance_counting\n your result\n {}\n is wrong for the set\n {}\n*****".format(R,S2))

test_min_max()
test_bounding_box()
test_maxima_set()
test_dominance_counting()

