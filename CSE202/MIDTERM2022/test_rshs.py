from math import sqrt
from rshs import *

def oneMax(x):
    om = 0
    for bit in x:
        om += bit
    return om

def leadingOnes(x):
    lo = 0
    for bit in x:
        if bit == 1:
            lo += 1
        else:
            break
    return lo

def testCreatingBitString():
    f = createBitStringUniformly
    print("\nTesting \033[34m{}\033[0m.".format(f.__name__))
    if f(20) == None:
        print("  \033[33mNot implemented.\033[0m Skipping test.")
        return

    fail = False
    miss = 0
    n = 200
    for _ in range(100):
        om = oneMax(f(n))
        if om < n / 2 - 2.5 * sqrt(n):
            print("  \033[31mWarning!\033[0m Your bit string contains too few 1s.")
            miss += 1
            fail = True
        elif om > n / 2 + 2.5 * sqrt(n):
            print("  \033[31mWarning!\033[0m Your bit string contains too many 1s.")
            miss += 1
            fail = True
        if miss >= 10:
            print("  \033[31mToo many warnings!\033[0m Stopping further tests.")
            break

    if not fail:
        print("  \033[32mSuccess!\033[0m Tests passed.")

def testSingleBitFlip():
    def positionOfOne(x, y):
        for i in range(len(x)):
            if x[i] != y[i]:
                return i
        assert False

    f = singleBitFlip
    print("\nTesting \033[34m{}\033[0m.".format(f.__name__))
    if f([0]) == None:
        print("  \033[33mNot implemented.\033[0m Skipping test.")
        return

    n = 200
    freqs = [0] * n
    x = [0] * (n // 2) + [1] * (n // 2)
    trials = 100
    for _ in range(trials):
        y = f(x)
        xOM = oneMax(x)
        yOM = oneMax(y)
        if len(x) != len(y):
            print("  \033[31mError!\033[0m Your result has a different length than the input.")
            quit()
        if abs(xOM - yOM) != 1:
            print("  \033[31mError!\033[0m Your mutation changes more than a single bit.")
            quit()
        freqs[positionOfOne(x, y)] += 1

    fail = False
    miss = 0
    l = 15
    assert l ** 2 * n / (trials * (1 - 1 / n)) >= l
    for i in range(len(freqs)):
        freq = freqs[i]
        if freq >= trials / n + l:
            print("  \033[31mWarning!\033[0m Position {} is flipped too many times.".format(i))
            miss += 1
            fail = True
        if miss >= 10:
            print("  \033[31mToo many warnings!\033[0m Stopping further tests.")
            break

    if not fail:
        print("  \033[32mSuccess!\033[0m Tests passed.")

def testStandardBitMutation():
    def positionOfOnes(x, y, freqs):
        diff = 0
        for i in range(len(x)):
            if x[i] != y[i]:
                freqs[i] += 1
                diff += 1
        return diff

    f = standardBitMutation
    print("\nTesting \033[34m{}\033[0m.".format(f.__name__))
    if f([0]) == None:
        print("  \033[33mNot implemented.\033[0m Skipping test.")
        return

    n = 200
    freqs = [0] * n
    x = [0] * (n // 2) + [1] * (n // 2)
    trials = 100
    l = 15
    fail = False
    miss = 0
    for _ in range(trials):
        y = f(x)
        if len(x) != len(y):
            print("  \033[31mError!\033[0m Your result has a different length than the input.")
            quit()
        diff = positionOfOnes(x, y, freqs)
        if diff >= 1 + l:
            print("  \033[31mWarning!\033[0m Your mutation seems to flip too many bits.")
            fail = True
            miss += 1
        if miss >= 10:
            print("  \033[31mToo many warnings!\033[0m Stopping further tests.")
            return

    assert l ** 2 * n / (trials * (1 - 1 / n)) >= l
    for i in range(len(freqs)):
        freq = freqs[i]
        if freq >= trials / n + l:
            print("  \033[31mWarning!\033[0m Position {} is flipped too many times.".format(i))
            miss += 1
            fail = True
        if miss >= 10:
            print("  \033[31mToo many warnings!\033[0m Stopping further tests.")
            break

    if not fail:
        print("  \033[32mSuccess!\033[0m Tests passed.")

def testRSHs():
    def terminated(x, it):
        if (oneMax(x) == len(x)) or it >= 50000:
            return True
        return False


    for m in [singleBitFlip, standardBitMutation]:
        factor = 1
        if m == singleBitFlip:
            print("\nTesting \033[34mRLS\033[0m.")
        else:
            print("\nTesting \033[34m(1 + 1) EA\033[0m.")
            factor = 2.7
        if rsh(10, oneMax, lambda x, y: True, m) == None:
            print("  \033[33mNot implemented.\033[0m Skipping test.")
            continue

        l1 = 100
        l2 = 45
        miss = 0
        fail = False
        for f in [oneMax, leadingOnes]:
            for _ in range(50):
                (_, time) = rsh(50, f, terminated, m)
                factor2 = 50
                if f == oneMax:
                    factor2 = 4
                if time >= factor * factor2 * (50 + l1):
                    print("  \033[31mWarning!\033[0m Your algorithm seems to take too long.")
                    fail = True
                    miss += 1
                elif time <= factor * factor2 * (50 - l2):
                    print("  \033[31mWarning!\033[0m Your algorithm seems to be too fast.")
                    fail = True
                    miss += 1
                if miss >= 10:
                    print("  \033[31mToo many warnings!\033[0m Stopping further tests.")
                    break
            if fail: break

        if not fail:
            print("  \033[32mSuccess!\033[0m Tests passed.")




## Tests
testCreatingBitString()   # Question 7
testSingleBitFlip()       # Question 8
testStandardBitMutation() # Question 9
testRSHs()                # Question 10. May take some time!