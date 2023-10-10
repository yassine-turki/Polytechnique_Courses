# -*- coding: utf-8 -*-
from search import *

import timeit
from datetime import datetime
import random
import matplotlib.pyplot as plt

grading_mode = False

## Q1 ##
def compare_rec_while(size, nb_tests):
    total_rec = 0
    total_while = 0
    for i in range(nb_tests):
        A = random.sample(range(100, 100 + 10*size), size)
        A.sort()
        if ( i%2 == 0 ):
            v = random.choice(A)
        else:
            v = 1
        def doit_rec():
            return binary_search_rec(A,v,0,len(A)-1)
        def doit_while():
            return binary_search(A,v)
        total_rec += timeit.timeit(doit_rec,number=1)
        total_while += timeit.timeit(doit_while,number=1)
    print("Average time: recursive = {}, iterative = {}".format(total_rec/nb_tests,total_while/nb_tests))
    
## Q2 ##
def compare_binary_ternary(n):
    N = [i for i in range(n)]
    implemented_B = cost_binary_search(1) is not None
    implemented_T = cost_ternary_search(1) is not None
    implemented_BR = cost_binary_search_real(N,1) is not None
    implemented_TR = cost_ternary_search_real(N,1) is not None

    B = T = BR = TR = []
    if implemented_B: B = [cost_binary_search(i) for i in range(n)]
    if implemented_T: T = [cost_ternary_search(i) for i in range(n)]

    if implemented_BR: BR = [0 for i in range(n)]
    if implemented_TR: TR = [0 for i in range(n)]

    if implemented_TR or implemented_BR:
        for i in range(1, n):
            brcost = trcost = 0
            nb_tries = 100
            for _ in range(nb_tries):
                A = random.sample(range(100, 100 + 10*n), i)
                A.sort()
                v = random.choice(A)
                if implemented_BR: brcost += cost_binary_search_real(A,v)
                if implemented_TR: trcost += cost_ternary_search_real(A,v)
            if implemented_BR: BR[i] = brcost/nb_tries
            if implemented_TR: TR[i] = trcost/nb_tries

    if implemented_B: plt.plot(N,B,'b')
    if implemented_BR: plt.plot(N,BR,'b')
    if implemented_T: plt.plot(N,T,'r')
    if implemented_TR: plt.plot(N,TR,'r')
    plt.show()
    
## Q5 ##
def compare_all(size, nb_tests):
    implemented_B = binary_search([1],1) is not None
    implemented_T = ternary_search([1],1) is not None
    implemented_E = exponential_search([1],1) is not None
    implemented_I = interpolation_search([1],1) is not None

    if (not (implemented_B or implemented_T or implemented_E or implemented_I)):
        return

    total_b = total_t = total_e = total_i = 0
    for i in range(nb_tests):
        A = random.sample(range(100, 100+10*size), size)
        A.sort()
        if ( i%2 == 0 ):
            v = random.choice(A)
        else:
            v = 1
        def doit_binary():
            return binary_search(A,v) if implemented_B else None
        def doit_ternary():
            return ternary_search(A,v) if implemented_T else None
        def doit_exponential():
            return exponential_search(A,v) if implemented_E else None
        def doit_interpolation():
            return interpolation_search(A,v) if implemented_I else None

        total_b += timeit.timeit(doit_binary,number=1)
        total_t += timeit.timeit(doit_ternary,number=1)
        total_e += timeit.timeit(doit_exponential,number=1)
        total_i += timeit.timeit(doit_interpolation,number=1)
        
    print("""Average execution times:
        binary        = {},
        ternary       = {},
        exponential   = {},
        interpolation = {}""".
        format(total_b/nb_tests, total_t/nb_tests, total_e/nb_tests, total_i/nb_tests))

def any_unimplemented(functions):
    for function in functions:
        if function([1], 0) is None:
            return True
    return False
        
def test_searches(name, func):
    if func([1],0) is None:
        print("skipping {} (unimplemeneted)".format(name))
        assert not grading_mode
        return
    nb_tests = 5
    size = 10
    for i in range(nb_tests):
        A = random.sample(range(100, 100 + 10*size), size)
        A.sort()
        if ( i%2 == 0 ):
            j = random.randrange(0,size-1)
            v = A[j]
        else:
            j = -1
            v = 1
        res = func(A,v)
        if (res != j):
            print("{}: wrong result for A={} and v={}: it should be {} but is {}".format(name,A,v,j,res))
            assert not grading_mode
            return False
    return True

def test1():
    print("Testing Q1...", end=" ")
    result = test_searches("binary_search", binary_search)
    if result is None: 
        return
    elif result:
        print("[OK]")
    else:
        print("[NOK]")
    compare_rec_while(200,5)

def test2():
    print('Testing Q2...', end=" ")
    result = test_searches("ternary_search", ternary_search)
    if result is None: 
        return
    elif result:
        print("[OK]")
    else:
        print("[NOK]")
    compare_binary_ternary(100)

def test3():
    print('Testing Q3...', end=" ")
    result = test_searches("exponential_search", exponential_search)
    if result is None: 
        return
    elif result:
        print("[OK]")
    else:
        print("[NOK]")

def test4():
    print('Testing Q4...', end=" ")
    result = test_searches("interpolation_search", interpolation_search)
    if result is None: 
        return
    elif result:
        print("[OK]")
    else:
        print("[NOK]")

## Q5 ##
def test5():
    print('Testing Q5...', end=" ")
    if any_unimplemented([binary_search, ternary_search, exponential_search, interpolation_search]):
        print('skipping comparison (some search algorithms are unimplemented)')
        return
    size = 100000
    print('comparing on arrays of size {}...'.format(size), end = " ", flush = True)
    compare_all(size,20)

## Q6 ##
def test6():
    print('Testing Q6...')

    def test_first_last (name, func, A, k, correct):
        result = func(A, k)
        if result is None: return
        if result == correct: 
            return True
        else:
            print ("wrong {} for {} in {}: {} instead of {}".format(name, k, A, result, correct))
            return False

    A = [1, 2, 3, 4, 5, 5, 6, 7, 8, 9]
    result = test_first_last("findFirstOccurrence", findFirstOccurrence, A, 5, 4)
    if result is None:
        print("skipping findFirstOccurrence (unimplemeneted)")
        assert not grading_mode
    elif result:
        print("findFirstOccurrence [OK]")
    else:
        print("findFirstOccurrence [NOK]")

    result = test_first_last("findLastOccurrence", findLastOccurrence, A, 5, 5)
    if result is None:
        print("skipping findLastOccurrence (unimplemeneted)")
        assert not grading_mode
    elif result:
        print("findLastOccurrence [OK]")
    else:
        print("findLastOccurrence [NOK]")


## Q7 ##
def test7():
    print('Testing Q7...', end=" ")

    def test_closest(A, v, k, correct):
        result = findKClosestElements(A, v, k)
        assert result is not None
        if result == correct:
            return True 
        else:
            print("wrong {} closest elements for {} in {}: {} instead of {}".format(k, v, A, result, correct))
            return False

    result = findKClosestElements([1],0,0)
    if result is None:
        print("skipping findKClosestElements (unimplemeneted)")
        assert not grading_mode
    else:
        A = [0, 2, 5, 7, 8, 11, 15]
        if (test_closest(A, 6, 4, [2, 5, 7, 8]) and
            test_closest(A, -1, 3, [0, 2, 5]) and 
            test_closest(A, 20, 2, [11, 15]) and
            test_closest(A, 7, 3, [5, 7, 8]) and
            test_closest(A, 1, 3, [0, 2, 5]) and
            test_closest(A, 14, 3, [8, 11, 15])
            ):
            print("[OK]")
        else:
            print("[NOK]")

## Q8 ##
def test8():
    print('Testing Q8...', end=" ")
    
    def test_frequency(A, result):
        freq = findFrequency(A)
        if freq is None:
            return
        elif freq == result:
            return True
        else:
            print("""wrong frequencies for {}: 
            {} instead of 
            {}""".
            format(A, freq, result)
            )
            return False

    A = [2,2,2,4,4,4,4,6,6,8,8,9]
    result = test_frequency(A, {2:3,4:4,6:2,8:2,9:1})
    if result is None:
        print("skipping findFrequency (unimplemeneted)")
        assert not grading_mode
    elif result:
        print("[OK]")
    else:
        print("[NOK]")

test1()
test2()
test3()
test4()
test5()
test6()
test7()
test8()