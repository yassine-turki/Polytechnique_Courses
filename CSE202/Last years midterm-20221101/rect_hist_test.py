# -*- coding: utf-8 -*-
# this file is designed to import rect_hist.py
if __name__ != '__main__':
    assert False, "You must NOT import this file from rect_hist.py"

import rect_hist as sol
import timeit
import random

grading_mode = False # set to True to make unimplemented function error out

def random_hist(n):
    """generate a random instance"""
    return [random.randint(1, n) for _ in range(n)]

def check(fn, hist, value):
    res = fn(hist)
    if res == value:
        return
    print("Test failure")
    print("Histogram: {}".format(hist))
    print("Expected value: {}".format(value))
    print("Returned value: {}".format(res))
    assert False, "test failure, see error message before traceback"

def check_exp(fn, hist, param, value):
    res = fn((*(hist,) + param))
    if res == value:
        return
    print("Test failure")
    print("Histogram: {}".format(hist))
    print("Expansion arguments: {}".format(param))
    print("Expected value: {}".format(value))
    print("Returned value: {}".format(res))
    assert False, "test failure, see error message before traceback"

def test_rect_left():
    if sol.rect_from_left([0], 0) is None:
        print('skipping rect_from_left (unimplemented)')
        assert not grading_mode
        return
    print('testing rect_from_left...')
    check_exp(sol.rect_from_left, [1, 3, 3, 5, 6, 6, 4, 6, 4, 2], (5,), 16)
    check_exp(sol.rect_from_left, [2, 1, 5, 6, 2, 3], (3,), 6)
    check_exp(sol.rect_from_left, [6, 1, 5, 4, 5, 2, 6], (2,), 12)
    check_exp(sol.rect_from_left, [1, 1, 1, 1, 1, 1, 1], (0,), 7)
    check_exp(sol.rect_from_left, [1, 1, 1, 100, 1, 1, 1], (0,), 7)
    # run it on a big-ish example to test complexity
    time = timeit.timeit(lambda: sol.rect_from_left([n for n in range(30000)], 0), number=1)
    if time >= 1:
        print("Your function took more than 1 second on an array of size 30000,")
        print("probably it has complexity O(n^2) instead of O(n)")
        assert False, "test failure, see error message before traceback"
    print('test passed')

# =========================================================================
# uncomment to test your code
test_rect_left()
# =========================================================================

def test_brute():
    if sol.rect_hist_brute([0]) is None:
        print('skipping rect_hist_brute (unimplemented)')
        assert not grading_mode
        return
    print('testing rect_hist_brute...')
    check(sol.rect_hist_brute, [2, 1, 5, 6, 2, 3], 10)
    check(sol.rect_hist_brute, [6, 1, 5, 4, 5, 2, 6], 12)
    check(sol.rect_hist_brute, [1, 1, 1, 1, 1, 1, 1], 7)
    check(sol.rect_hist_brute, [1, 1, 1, 100, 1, 1, 1], 100)
    # run it on a big-ish example to test complexity
    time = timeit.timeit(lambda: sol.rect_hist_brute([n for n in range(700)]), number=1)
    if time >= 1:
        print("Your function took more than 1 second on an array of size 700,")
        print("probably it has complexity O(n^3) instead of O(n^2)")
        assert False, "test failure, see error message before traceback"
    print('test passed')

# =========================================================================
# uncomment to test your code
test_brute()
# =========================================================================

L_example = [1,3,3,5,6,6,4,6,4,2]

def test_expand_rect():
    if sol.expand_rect([1,1],0,1,0,0,1) is None:
        print('skipping expand_rect (unimplemented)')
        assert not grading_mode
        return
    print("testing expand_rect...")
    check_exp(sol.expand_rect, L_example, (0, 10, 4, 5, 6), (4,6,6))
    check_exp(sol.expand_rect, L_example, (0, 10, 4, 6, 6), (3,6,5))
    check_exp(sol.expand_rect, L_example, (0, 10, 3, 6, 5), (3,7,4))
    check_exp(sol.expand_rect, L_example, (0, 10, 3, 7, 4), (3,8,4))
    check_exp(sol.expand_rect, L_example, (0, 10, 3, 8, 4), (3,9,4))
    check_exp(sol.expand_rect, L_example, (0, 10, 3, 9, 4), (2,9,3))
    check_exp(sol.expand_rect, L_example, (0, 10, 2, 9, 3), (1,9,3))
    check_exp(sol.expand_rect, L_example, (0, 10, 1, 9, 3), (1,10,2))
    check_exp(sol.expand_rect, L_example, (0, 10, 1, 10, 2), (0,10,1))
    # more expansions
    check_exp(sol.expand_rect, L_example, (0, 8, 3, 8, 4), (2,8,3))
    check_exp(sol.expand_rect, L_example, (2, 10, 2, 9, 3), (2,10,2))
    # run it on a big-ish example to test complexity
    n = 10000000
    L_big = [n for n in range(n)]
    def test():
        check_exp(sol.expand_rect, L_big, (0, n, 1, n-1, 1), \
                                    (1, n, 1))
    time = timeit.timeit(test, number=1)
    if time >= 0.001:
        print("Your function took more than 1 millisecond on an array of size 10^7,")
        print("probably it has complexity O(n) instead of O(1)")
        assert False, "test failure, see error message before traceback"
    print('test passed')

# =========================================================================
# uncomment to test your code
test_expand_rect()
# =========================================================================

def test_from_middle():
    if sol.best_from_middle([1,1],0,1,0) is None:
        print('skipping best_from_middle (unimplemented)')
        assert not grading_mode
        return
    print("testing best_from_middle...")
    check_exp(sol.best_from_middle, L_example, (0, 10, 4), 24)
    check_exp(sol.best_from_middle, L_example, (2, 8, 4), 20)
    #check_exp(sol.best_from_middle, L_example, (1, 2, 2), 3)
    check_exp(sol.best_from_middle, L_example, (1, 2, 1), 3)
    check_exp(sol.best_from_middle, L_example, (0, 2, 1), 3)
    check_exp(sol.best_from_middle, L_example, (7, 8, 7), 6)
    check_exp(sol.best_from_middle, L_example, (6, 8, 7), 8)
    check_exp(sol.best_from_middle, L_example, (7, 9, 7), 8)
    print('test passed')

# =========================================================================
# uncomment to test your code
test_from_middle()
# =========================================================================

def test_dac():
    if sol.rect_hist_dac([1,1]) is None:
        print('skipping rect_hist_dac (unimplemented)')
        assert not grading_mode
        return
    print('testing rect_hist_dac...')
    check(sol.rect_hist_dac, [2, 1, 5, 6, 2, 3], 10)
    check(sol.rect_hist_dac, [6, 1, 5, 4, 5, 2, 6], 12)
    check(sol.rect_hist_dac, [6, 2, 3, 4, 2, 5, 5, 5, 3, 6], 20)
    # run it on a big-ish example to test complexity
    n = 5001 # make sure it's odd
    L_big = [n+1 for n in range(n)]
    def test():
        check(sol.rect_hist_dac, L_big, (n+1)**2//4)
    time = timeit.timeit(test, number=1)
    if time >= 1:
        print("Your function took more than 1 second on an array of size 5000,")
        print("probably it has complexity O(n^2) instead of O(nlog(n))")
        assert False, "test failure, see error message before traceback"
    print("testing random instances...")
    for n in range(1, 5):
        for _ in range(100):
            L = random_hist(n)
            check(sol.rect_hist_dac, L, sol.rect_hist_brute(L))
    for _ in range(100):
        L = random_hist(1000)
        check(sol.rect_hist_dac, L, sol.rect_hist_brute(L))
    print("test passed")

# =========================================================================
# uncomment to test your code
test_dac()
# =========================================================================
