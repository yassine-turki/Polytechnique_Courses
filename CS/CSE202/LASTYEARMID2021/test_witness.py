# -*- coding: utf-8 -*-

import numpy as np
from Test2 import *

grading_mode = False

def inclusion_matrix(A1,A2):
    n = len(A1)
    for i in range(n):
        for j in range(n):
            if (A1[i][j]>0 and A1[i][j] not in A2[i][j]):
                print("{},{}".format(i,j))
                return False
            if (A1[i][j] == 0 and len(A2[i][j])>0):
                print("{},{}".format(i,j))
                return False
    return True

def equal_matrix(A1,A2):
    n = len(A1)
    m = len(A2)
    if (m != n):
        return False
    for i in range(n):
        for j in range(n):
            if (A1[i][j]!=A2[i][j]):
                return False
    return True
    
def compute_witness_complete(A,B):
    n = len(A)
    W = [[[] for i in range(n)] for j in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if (A[i][k] == 1 and B[k][j] == 1):
                    W[i][j].append(k+1)
    return W

A1 = [[1,1,0],[1,1,0],[0,1,0]]
B1 = [[1,0,1],[0,1,0],[0,1,0]]

A2 = [[1,0,1,0],[0,0,1,1],[0,1,0,1],[0,1,1,0]]
B2 = [[1,1,1,1],[0,1,0,1],[0,0,1,1],[0,0,0,1]]

A3 = [[1,1],[1,0]]
B3 = [[0,1],[1,0]]

AB3 = [[1,1,1],[1,1,1],[1,1,1]]
AB4 = [[0,0,0],[0,0,0],[0,0,0]]

def check_witness(func,A,B):
    T1 = func(A,B)
    T2 = compute_witness_complete(A,B)
    if (not inclusion_matrix(T1,T2)):
        print("***** {}\n your result\n {}\n should be included (component-wise) in\n {}\n*****".format(func.__name__,T1,T2))
        assert not grading_mode

def test_compute_witness_trivial():
    if compute_witness_trivial(A1,B1) is None:
        print("***** skipping compute_witness_trivial (unimplemented)")
        assert not grading_mode
        return
    check_witness(compute_witness_trivial,A1,B1)
    check_witness(compute_witness_trivial,A2,B2)
    check_witness(compute_witness_trivial,AB3,AB3)
    check_witness(compute_witness_trivial,AB4,AB4)

def test_expose():
    if expose(A1) is None:
        print("***** skipping expose_column (unimplemented)")
        assert not grading_mode
        return
    A = [[0,1,1],[1,1,0],[0,0,1]]
    T1 = expose(A)
    T2 = [[0,2,3],[1,2,0],[0,0,3]]
    if (not equal_matrix(T1,T2)):
        print("***** expose_column\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode
    T1 = expose(AB3)
    T2 = [[1,2,3],[1,2,3],[1,2,3]]
    if (not equal_matrix(T1,T2)):
        print("***** expose_column\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode
        
def test_compute_witness_unique():
    if compute_witness_unique(A1,B1) is None:
        print("***** skipping compute_witness_unique (unimplemented)")
        assert not grading_mode
        return
    check_witness(compute_witness_unique,A3,B3)
    check_witness(compute_witness_unique,AB4,AB4)
    
def test_nullify_rows():
    if nullify_rows(AB3,[1,3]) is None:
        print("***** skipping nullify_rows (unimplemented)")
        assert not grading_mode
        return
    T1 = nullify_rows(AB3,[1,3])
    T2 = [[1,1,1],[0,0,0],[1,1,1]]
    if (not equal_matrix(T1,T2)):
        print("***** nullify_rows\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode
    T1 = nullify_rows(AB3,[2,3])
    T2 = [[0,0,0],[1,1,1],[1,1,1]]
    if (not equal_matrix(T1,T2)):
        print("***** nullify_rows\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode
    T1 = nullify_rows(AB3,[1,2,3])
    if (not equal_matrix(T1,AB3)):
        print("***** nullify_rows\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode

def test_nullify_columns():
    if nullify_columns(AB3,[1,3]) is None:
        print("***** skipping nullify_columns (unimplemented)")
        assert not grading_mode
        return
    T1 = nullify_columns(AB3,[1,3])
    T2 = [[1,0,1],[1,0,1],[1,0,1]]
    if (not equal_matrix(T1,T2)):
        print("***** nullify_columns\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode
    T1 = nullify_columns(AB3,[2,3])
    T2 = [[0,1,1],[0,1,1],[0,1,1]]
    if (not equal_matrix(T1,T2)):
        print("***** nullify_columns\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode
    T1 = nullify_columns(AB3,[1,2,3])
    if (not equal_matrix(T1,AB3)):
        print("***** nullify_columns\n your result\n {}\n is different from the expected\n {}\n*****".format(T1,T2))
        assert not grading_mode

def check_witness_restricted(func,A,B,R):
    T1 = func(A,B,R)
    T2 = compute_witness_complete(A,B)
    for i in range(len(T2)):
        for j in range(len(T2)):
            for k in range(len(T2)):
                if (k not in R and k in T2[i][j]):
                    T2[i][j].remove(k)
    if (not inclusion_matrix(T1,T2)):
        print("***** {}\n your result\n {}\n should be included (component-wise) in\n {}\n*****".format(func.__name__,T1,T2))
        assert not grading_mode

def test_compute_witness_restricted():
    if compute_witness_restricted(A1,B1,[1]) is None:
        print("***** skipping compute_witness_restricted (unimplemented)")
        assert not grading_mode
        return
    check_witness_restricted(compute_witness_restricted,A1,B1,[1,3])
    check_witness_restricted(compute_witness_restricted,A1,B1,[2,3])
    check_witness_restricted(compute_witness_restricted,AB4,AB4,[1,2,3])
    check_witness_restricted(compute_witness_restricted,AB4,AB4,[1,2])

def test_sample():
    if sample(3,10) is None:
        print("***** skipping sample (unimplemented)")
        assert not grading_mode
        return
    R = []
    for _ in range(10):
        T = sample(4,10)
        for i in range(4):
            if (T[i] < 1 or T[i] > 10):
                print("***** sample\n your result\n {}\n contains incorrect value {}\n*****".format(T,T[i]))
        R.append(T)
    eq = [False for i in range(4)]
    for i in range(4):
        eq[i] = True
        for j in range(len(R)):
            if (R[j][i] != R[0][i]):
                eq[i] = False
                break
    for i in range(4):
        if (not eq[i]):
            return
    print("***** sample\n something is wrong with your result as it repeats the same values\n {}\n*****".format(R))

def test_compute_witness_random(t,n):
    if compute_witness_random(A1,B1) is None:
        print("***** skipping compute_witness_random (unimplemented)")
        assert not grading_mode
        return
    check_witness(compute_witness_random,A1,B1)
    check_witness(compute_witness_random,A2,B2)
    check_witness(compute_witness_random,AB3,AB3)
    check_witness(compute_witness_random,AB4,AB4)
    total_trivial = 0
    total_random = 0
    for _ in range(t):
        A = [[0 for i in range(n)] for j in range(n)]
        B = [[0 for i in range(n)] for j in range(n)]
        for i in range(n):
            for j in range(n):
                A[i][j] = random.randint(0,1)
                B[i][j] = random.randint(0,1)
        check_witness(compute_witness_random,A,B)
    

# test_compute_witness_trivial()
# test_expose()
# test_compute_witness_unique()
# test_nullify_rows()
# test_nullify_columns()
# test_compute_witness_restricted()
# test_sample()
test_compute_witness_random(10,10)

