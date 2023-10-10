import random
import matplotlib.pyplot as plt

import L_tiling as til

def test1():
    if til.middleL(4, 5, 7, 15, 9) is None:
        print("skipping middleL (unimplemented)")
        return
    
    def sort_and_test(inputs, solutions):
        success = True
        for i in range(len(inputs)):
            tmp = til.middleL(*inputs[i])
            tmp.sort()
            if tmp != solutions[i]:
                print("-- Your function middleL returned the wrong result ({} instead of {})".format(tmp, solutions[i]))
                success = False
        return success
    
    success = sort_and_test([(4, 5, 7, 15, 9), (2, 1, 3, 4, 5)], [[(12, 14), (12, 15), (13, 15)], [(2, 4), (2, 5), (3, 4)]])

    if success:
        print("++ Test success for middleL.")

def test2():
    def test_function(getHole, name, inputs, solutions):
        if getHole(4, 5, 7, 15, 9) is None:
            print("skipping {} (unimplemented)".format(name))
            return
        success = True
        for i in range(len(inputs)):
            hole = getHole(*inputs[i])
            if hole != solutions[i]:
                print("-- Your function {} returned the wrong result ({} instead of {})".format(name, hole, solutions[i]))
                success = False
        if success:
            print("++ Test success for {}.".format(name))
    # lower_left_hole
    test_function(til.lower_left_hole, "lower_left_hole", [(4, 5, 7, 15, 9), (4, 5, 7, 7, 8)], [(12, 14), (7, 8)])
    
    # lower_right_hole
    test_function(til.lower_right_hole, "lower_right_hole", [(4, 5, 7, 15, 9), (4, 5, 7, 7, 8)], [(15, 9), (13, 14)])

    # upper_left_hole
    test_function(til.upper_left_hole, "upper_left_hole", [(4, 5, 7, 6, 18), (4, 5, 7, 7, 8)], [(6, 18), (12, 15)])
    
    # upper_right_hole
    test_function(til.upper_right_hole, "upper_right_hole", [(4, 5, 7, 15, 19), (4, 5, 7, 7, 8)], [(15, 19), (13, 15)])

def test3():
    tmp = til.tile(3, 1, 2, 6, 4)
    if tmp == None:
        print("skipping tile (unimplemented)")
        return
    for L in tmp:
            L.sort()
    tmp.sort()	
    res = [[(1, 2), (1, 3), (2, 2)], [(1, 4), (1, 5), (2, 5)], [(1, 6), (1, 7), (2, 6)], [(1, 8), (1, 9), (2, 9)], [(2, 3), (2, 4), (3, 3)], [(2, 7), (2, 8), (3, 8)], [(3, 2), (4, 2), (4, 3)], [(3, 4), (3, 5), (4, 4)], [(3, 6), (3, 7), (4, 7)], [(3, 9), (4, 8), (4, 9)], [(4, 5), (4, 6), (5, 6)], [(5, 2), (5, 3), (6, 2)], [(5, 4), (5, 5), (6, 5)], [(5, 7), (6, 6), (6, 7)], [(5, 8), (5, 9), (6, 9)], [(6, 3), (7, 3), (7, 4)], [(6, 8), (7, 7), (7, 8)], [(7, 2), (8, 2), (8, 3)], [(7, 5), (8, 4), (8, 5)], [(7, 6), (8, 6), (8, 7)], [(7, 9), (8, 8), (8, 9)]]
    if tmp != res:
        print("Your function tile returned the wrong result ({} instead of {})".format(tmp, res))
        return
    print("++ Test success for tile.")

def display_tiling_with_random_hole(n):
    N = 2 ** n
    tmp = til.tile(n, 0, 0, random.randrange(N), random.randrange(N))
    data = [[[0,0,0] for _ in range(N)] for _ in range(N)]
    for L in tmp:
        r = random.randrange(256)
        g = random.randrange(256)
        b = random.randrange(256)
        for entry in L:
            data[entry[0]][entry[1]] = [r, g, b]
    plt.imshow(data, origin = 'lower')
    plt.show()

# Tests

test1()
test2()
test3()
display_tiling_with_random_hole(4)
