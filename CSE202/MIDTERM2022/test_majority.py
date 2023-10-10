from majority import *

def testFunction(f, testPairs):
    print("\nTesting \033[34m{}\033[0m.".format(f.__name__))
    if f(*testPairs[0][0]) == None:
        print("  \033[33mNot implemented.\033[0m Skipping test.")
        return
    for test in testPairs:
        result = f(*test[0])
        if result != test[1]:
            print("  \033[31mError\033[0m: The result for {} should be {}, but is instead {}."
                .format(test[0], test[1], result)
            )
            quit()
    print("  \033[32mSuccess!\033[0m Tests passed.")

def testFrequencies():
    a = [1, 15, 2, 1, -9]
    testPairs = [
        ((15, [0, 1], 0, 2),
          False),
        ((1, a, 0, 4),
          2),
        ((1, a, 1, 4),
          1)
    ]
    testFunction(getFrequency, testPairs)

def testNaive():
    repeat = 4
    testPairs = [
        (([15, 13, 15],), 15),
        (([*range(3)] * repeat,), False),
        (([0, -1, -1] * repeat,), -1)
    ]
    testFunction(getMajorityNaively, testPairs)

def testDivideAndConquer():
    repeat = 4
    testPairs = [
        (([4, 4, 6],), 4),
        (([*range(2, -1, -1)] * repeat,), False),
        (([0, 8, 8] * repeat,), 8)
    ]
    testFunction(getMajorityDaC, testPairs)

def testMatrixDivideAndConquer():
    testPairs = [
        (([[0, 0], [0, 1]],), 0),
        (([[0, 0, 1, 1], [0, 1, 1, 0], [1, 1, 0, 0], [1, 0, 0, 1]],), False),
        (([[1, 0, 1, 1], [0, 1, 1, 0], [1, 1, 0, 0], [1, 0, 0, 1]],), 1)
    ]
    testFunction(getMajorityInMatrixDaC, testPairs)

def testBoyerMoore():
    testPairs = [
        (([17, 23, -19, 23],), False),
        (([17, 23, -19, 23, 17, 17],), False),
        (([17, 17, -19, 17, 23, 17],), 17),
    ]
    testFunction(getMajorityBoyerMoore, testPairs)

def testRandomized():
    f = getMajorityRandomized
    print("\nTesting \033[34m{}\033[0m.".format(f.__name__))
    if f([1], 0) == None:
        print("  \033[33mNot implemented.\033[0m Skipping test.")
        return

    fail = False
    # First test.
    succ = 0
    v = 34
    L = [v, -5, v, v, 21, v, 15, 6, v, 24, v, 9, 27, v, v, v, -3, v, 17]
    for _ in range(113):
        if f(L, 3 / 4) == v:
            succ += 1
    if succ < 72:
        print("  \033[31mWarning!\033[0m Your code seems to fail too often.")
        fail = True
    elif succ > 97:
        print("  \033[31mWarning!\033[0m Your code seems to succeed too often.")
        fail = True

    #Second test.
    succ = 0
    L = [27, 12, 20, 22, 7, 17, 21, 19, 8, -2]
    for _ in range(113):
        if f(L, 3 / 4) != False:
            succ += 1
    if succ > 0:
        print("  \033[31mError\033[0m: Your code finds a majority element for {}.".format(L))
        fail = True

    if not fail:
        print("  \033[32mSuccess!\033[0m Tests passed.")


## Tests
testFrequencies()            # Question 1
testNaive()                  # Question 2
testDivideAndConquer()       # Question 3
#testMatrixDivideAndConquer() # Question 4
testBoyerMoore()             # Question 5
testRandomized()             # Question 6