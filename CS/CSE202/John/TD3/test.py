# -*- coding: utf-8 -*-
from search import *

import timeit
from datetime import datetime
import random
import matplotlib.pyplot as plt
from collections import Counter

grading_mode = False

## Q1 ##
def compare_rec_while(size,nb_tests):
    total_rec = 0
    total_while = 0
    for i in range(nb_tests):
        A = random.sample(range(100, 1000000), size)
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
    B = [cost_binary_search(i) for i in range(n)]
    T = [cost_ternary_search(i) for i in range(n)]
    plt.plot(N,B,'b')
    plt.plot(N,T,'r')
    plt.show()
    
## Q5 ##
def compare_all(size,nb_tests):
    total_b = total_t = total_e = total_i = 0
    for i in range(nb_tests):
        A = random.sample(range(100, 1000000), size)
        A.sort()
        if ( i%2 == 0 ):
            v = random.choice(A)
        else:
            v = 1
        def doit_binary():
            return binary_search(A,v)
        def doit_ternary():
            return ternary_search(A,v)
        def doit_exponential():
            return exponential_search(A,v)
        def doit_interpolation():
            return interpolation_search(A,v)

        total_b += timeit.timeit(doit_binary,number=1)
        total_t += timeit.timeit(doit_ternary,number=1)
        total_e += timeit.timeit(doit_exponential,number=1)
        total_i += timeit.timeit(doit_interpolation,number=1)
        
    print("Average time: binary = {}, ternary = {}, exponential = {}, interpolation = {}".format(total_b/nb_tests,total_t/nb_tests,total_e/nb_tests,total_i/nb_tests))
        


def test_searches(name, func):
    if func([1],0) is None:
        print("skipping {} (unimplemeneted)".format(name))
        assert not grading_mode
        return
    nb_tests = 5
    size = 10
    for i in range(nb_tests):
        A = random.sample(range(100, 1000000), size)
        A.sort()
        if ( i%2 == 0 ):
            j = random.randrange(0,size-1)
            v = A[j]
        else:
            j = -1
            v = 1
        res = func(A,v)
        if (res != j):
            print("\n!! {}: test {}, wrong result for A={} and v={}: it should be {} but is {}\n".format(name,i,A,v,j,res))
            assert not grading_mode 
        else : print("++ {} passed test {}".format(name,i))      

def test_first_occurence(func):
    if func([1],0) is None:
        print("skipping findFirstOccurrence (unimplemeneted)")
        assert not grading_mode
        return
    nb_tests = 5
    size = 10
    for i in range(nb_tests):
        A = [random.randint(2,6) for x in range(size)]
        A.sort()
        if ( i%2 == 0 ):
            j = random.randrange(0,size-1)
            v = A[j]
            while (A[j]==A[j-1] and j>0):
                j-=1
        else:
            j = -1
            v = 1
        res = func(A,v)
        if (res != j):
            print("\n!! findFirstOccurrence: test {}, wrong result for A={} and v={}: it should be {} but is {}\n".format(i,A,v,j,res))
            assert not grading_mode 
        else : print("++ findFirstOccurrence passed test {}".format(i))      

def test_last_occurence(func):
    if func([1],0) is None:
        print("skipping findLastOccurrence (unimplemeneted)")
        assert not grading_mode
        return
    nb_tests = 5
    size = 10
    for i in range(nb_tests):
        A = [random.randint(2,6) for x in range(size)]
        A.sort()
        if ( i%2 == 0 ):
            j = random.randrange(0,size-1)
            v = A[j]
            while (j<size-1 and A[j]==A[j+1]):
                j+=1
        else:
            j = -1
            v = 1
        res = func(A,v)
        if (res != j):
            print("\n!! findLastOccurrence: test {}, wrong result for A={} and v={}: it should be {} but is {}\n".format(i,A,v,j,res))
            assert not grading_mode 
        else : print("++ findLastOccurrence passed test {}".format(i)) 


def test_k_closest(func):
    if func([1],0,1) is None:
        print("skipping findKClosestElements (unimplemeneted)")
        assert not grading_mode
        return
    nb_tests = 6
    size = 10
    k = 4
    for i in range(nb_tests):
        A = [random.randint(2,6) for x in range(size)]
        A.sort()
        if ( i%3 == 0 ):
            j = random.randrange(0,size-1)
            v = A[j]
            tmp=[v]
            left=j
            right=j
            while (len(tmp)<k):
                if left==0:
                    tmp=tmp+[A[right+1]]
                    right+=1
                elif right==size-1:
                    tmp=[A[left-1]]+tmp
                    left -=1
                elif (v-A[left-1])<(A[right+1]-v):
                    tmp=[A[left-1]]+tmp
                    left -=1
                else:
                    tmp=tmp+[A[right+1]]
                    right +=1
            tmp2=[v]
            left=j
            right=j
            while (len(tmp2)<k):
                if left==0:
                    tmp2=tmp2+[A[right+1]]
                    right+=1
                elif right==size-1:
                    tmp2=[A[left-1]]+tmp2
                    left -=1
                elif (v-A[left-1])<=(A[right+1]-v):
                    tmp2=[A[left-1]]+tmp2
                    left -=1
                else:
                    tmp2=tmp2+[A[right+1]]
                    right +=1    
        elif ( i%3 == 1 ): 
            j= size
            v=A[size-1]+1
            tmp=A[size-k:size]
        else:
            j = -1
            v = 1
            tmp=A[0:k]
        res = func(A,v,k)
        if (res != tmp and res != tmp2):
            print("\n!! findKClosestElements: test {}, wrong result for A={} and v={} and k={}: it should be {} or {} but is {}\n".format(i,A,v,k,tmp,tmp2,res))
            assert not grading_mode 
        else : print("++ findKClosestElements passed test {}".format(i))
        
def test_frequency(func):    
    if func([1]) is None:
        print("skipping findFrequency (unimplemeneted)")
        assert not grading_mode
        return
    nb_tests = 4
    size = 10
    for i in range(nb_tests):
        A = [random.randint(1,5) for x in range(size)]
        A.sort()
        freq=dict(Counter(A))
        res = func(A)
        if (freq != res):
            print("\n!! findFrequency: test {}, wrong result for A={}: it should be {} but is {}\n".format(i,A,freq,res))
            assert not grading_mode 
        else : print("++ findFrequency passed test {}".format(i))

def test1():
    test_searches("binary_search", binary_search)
    
def test2():
    test_searches("ternary_search", ternary_search)
    
def test3():
    test_searches("exponential_search", exponential_search)

def test4():
    test_searches("interpolation_search", interpolation_search)

def test5():
    test_first_occurence(findFirstOccurrence)
    
def test6():
    test_last_occurence(findLastOccurrence)    
    
def test7():
    test_k_closest(findKClosestElements)

def test8():
    test_frequency(findFrequency)

test1()
test2()
test3()
test4()
test5()
test6()
test7()
test8()

# To call for question 1
# compare_rec_while(200,5)

# To call for question 2
# compare_binary_ternary(100)

# To call for question 5
# compare_all(100000,20)



