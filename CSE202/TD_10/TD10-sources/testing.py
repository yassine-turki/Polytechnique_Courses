import math
import retrieval

count = 0

def prepare_dist(filename):
    file = open(filename, "r")
    T = int(file.readline())
    dim = int(file.readline())
    tests = []
    for _ in range(T):
        line = [float(x) for x in file.readline().split()]
        tests.append((tuple(line[:dim]), tuple(line[dim:-1]), line[-1]))

    file.close()
    return tests

def read_parameters(file):
    N = int(file.readline())
    dim = int(file.readline())
    T = int(file.readline())
    return N, dim, T

def prepare_cloud(file, N):
    P = []
    for _ in range(N):
        P.append(tuple([float(x) for x in file.readline().split()]))

    return P

def prepare_retrieval_tests(file, dim, T):
    tests = []
    for _ in range(T):
        line = [float(x) for x in file.readline().split()]
        tests.append((tuple(line[:dim]), int(line[-2]), line[-1]))

    return tests

def prepare_other_tests(file, T):
    tests = []
    for _ in range(T):
        line = file.readline().split()
        tests.append((int(line[0]), int(line[1]), int(line[2]), float(line[-1])))

    return tests

def test_dist(filename, epsilon, verbose = True):
    if retrieval.dist([0],[1]) is None:
        print("Skipping function dist() –- not implemented")
        return False

    print(f"Testing the function dist() using data from file '{filename}'...", end="\t")
    if verbose: print()

    tests = prepare_dist(filename)
    if verbose:
        print(f"\tLoaded {len(tests)} pairs of points of dimension {len(tests[0][0])}")

    nbErrors = 0
    for (p, q, dist) in tests:
        result = retrieval.dist(p, q)
        if result is None or math.fabs(dist - result) > epsilon:
            nbErrors += 1
            
            if verbose:
                print(f"\tFor points {p} and {q},")
                print(f"\t\tExpected distance {dist}")
                print(f"\t\tComputed distance {result}")

    success = (nbErrors == 0)
    print(f"{'[OK]' if success else '[NOK]'}")
    if verbose: print()

    return success

def test_median(filename, epsilon, verbose = True):
    if retrieval.compute_median([[0]],0,1,0) is None:
        print("Skipping function compute_median() –- not implemented")
        return False

    print(f"Testing method compute_median() using data from file '{filename}'...", end="\t")
    if verbose: print()

    file = open(filename, "r")
    N, dim, T = read_parameters(file)
    P = prepare_cloud(file, N)
    tests = prepare_other_tests(file, T)
    file.close()

    if verbose:
        print(f"\tLoaded {len(P)} points of dimension {len(P[0])} and {len(tests)} tests")

    nbErrors = 0
    for (start, end, coord, median) in tests:
        result = retrieval.compute_median(P, start, end, coord)
        if result is None or math.fabs(median - result) > epsilon:
            nbErrors += 1
            
            if verbose:
                print(f"\tFor the range[{start}..{end}] and coordinate {coord},")
                print(f"\t\tExpected median {median}")
                print(f"\t\tComputed median {result}")

    success = (nbErrors == 0)
    print(f"{'[OK]' if success else '[NOK]'}")
    if verbose: print()

    return success

def test_partition(filename, epsilon, verbose = True):
    if retrieval.partition([[0]],0,1,0) is None:
        print("Skipping function partition() –- not implemented")
        return False

    print(f"Testing method partition() using data from file '{filename}'...", end="\t")
    if verbose: print()

    file = open(filename, "r")
    N, dim, T = read_parameters(file)
    P = prepare_cloud(file, N)
    tests = prepare_other_tests(file, T)
    file.close()
    
    if verbose:
        print(f"\tLoaded {len(P)} points of dimension {len(P[0])} and {len(tests)} tests")

    nbErrorsMed = 0
    nbErrorsPart = 0
    for testIndex, (start, end, coord, median) in enumerate(tests):
        nberrmednow = 0
        nberrparnow = 0
        Q = P.copy()
        cmedian = retrieval.compute_median(Q, start, end, coord)
        if cmedian is None or math.fabs(median - cmedian) > epsilon:
            nberrmednow += 1

        index = retrieval.partition(Q, start, end, coord)

        # Check if to the left of median the elements are <=
        for i in range(start, index):
            if Q[i][coord] > cmedian:
                nberrparnow += 1

        # Check if the median is the median
        if math.fabs(Q[index][coord] - cmedian) > epsilon:
            nberrparnow += 1
        
        # Check if to the right of median the elements are >
        for i in range(index + 1, end):
            if Q[i][coord] - cmedian < epsilon:
                nberrparnow += 1

        if verbose and (nberrmednow > 0 or nberrparnow > 0):
            print(f"\tFor test {testIndex} the range[{start}..{end}] and coordinate {coord},")
            if nberrmednow > 0:
                print(f"\t\texpected median={median}, computed={cmedian}")
            if nberrparnow > 0:
                print(f"\t\t#errors = {nberrparnow} in partition computations")
            
        nbErrorsMed += nberrmednow
        nbErrorsPart += nberrparnow

    success = (nbErrorsMed == 0 and nbErrorsPart == 0)
    print(f"{'[OK]' if success else '[NOK]'}")
    if verbose: print()

    return success

def dump_tree (tree, P, prefix=""):
    if tree is None: return
    print(f"{prefix}{tree!r}->Point{P[tree.index]!r}")
    dump_tree(tree.left, P, prefix + "\t")
    dump_tree(tree.right, P, prefix + "\t")

def test_kdTree(verbose, P, tree, coord = None, median = None, left = None):
    success = True
    if coord is None or median is None or left is None:
        if not tree.left is None:
            success = success and test_kdTree(verbose, P, tree.left, tree.coord, tree.median, True)
        if not tree.right is None:
            success = success and test_kdTree(verbose, P, tree.right, tree.coord, tree.median, False)
        if verbose and not success:
            print(f"\tThe following sub-tree is not a kd-Tree:")
            dump_tree(tree, P, "\t")

        if not tree.left is None:
            success = success and test_kdTree(verbose, P, tree.left)
        if not tree.right is None:
            success = success and test_kdTree(verbose, P, tree.right)
    else:
        if left:
            success = success and (P[tree.index][coord] <= median)
        else:
            success = success and (P[tree.index][coord] > median)

        if not tree.left is None:
            success = success and test_kdTree(verbose, P, tree.left, coord, median, left) 
        if not tree.right is None:
            success = success and test_kdTree(verbose, P, tree.right, coord, median, left)

    return success

def test_build (filename, verbose = True):
    if retrieval.build([[0],[0]],0,2,0) is None:
        print("Skipping function build() –- not implemented")
        return False

    print(f"Testing the method build() using data from file '{filename}'...", end="\t")
    if verbose: print()

    file = open(filename, "r")
    N, dim, T = read_parameters(file)
    P = prepare_cloud(file, N)
    file.close()

    if verbose:
        print(f"\tLoaded {len(P)} points of dimension {len(P[0])}")

    kdTree = retrieval.build(P, 0, len(P), 0)
    success = test_kdTree(verbose, P, kdTree)

    print(f"{'[OK]' if success else '[NOK]'}")
    if verbose: print()

    return success

def test_retrieval(filename, method, epsilon, verbose = True):
    if method([0],[[0]]) is None:
        print(f"Skipping function {method.__name__}() –- not implemented")
        return False

    print(f"Testing retrieval method {method.__name__}() using data from file '{filename}'...", end="\t")
    if verbose: print()

    file = open(filename, "r")
    N, dim, T = read_parameters(file)
    P = prepare_cloud(file, N)
    tests = prepare_retrieval_tests(file, dim, T)
    file.close()

    if verbose:
        print(f"\tLoaded {len(P)} points of dimension {len(P[0])} and {len(tests)} tests")

    nbErrors = 0
    counts = []
    for i, (query, index, dist) in enumerate(tests):
        Q = P.copy()
        cindex, cdist = method(query, Q)
        counts.append(retrieval.count)
        if cindex is None or index != cindex:
            nbErrors += 1

            if verbose:
                print(f"\tFor query point {i}: {query},")
                # print("\t\tDistances to points in the cloud:")
                # for p in P:
                #     print(f"\t\t\tTo point {p}: {retrieval.dist(p, query)}")
                print(f"\t\tExpected nearest neighbour index and distance are {index} and {dist}")
                print(f"\t\tComputed index and distance are {cindex} and {cdist}")

    global count
    count = sum(counts)

    success = (nbErrors == 0)
    print(f"{'[OK]' if success else '[NOK]'}")
    if verbose: print()

    return success

# Test Question 1
def test_Q1(verbose, longTests, epsilon):
    if longTests:
        return \
            test_dist('./tests/dist_4.dat', epsilon, verbose) \
            and test_dist('./tests/dist_10.dat', epsilon, verbose) \
            and test_dist('./tests/dist_50.dat', epsilon, verbose)
    else:
        return test_dist('t_dist.dat', epsilon, verbose)

# Test Question 2
def test_Q2(verbose, longTests, epsilon):
    if longTests:
        return \
            test_retrieval('./tests/ls-1000-100-100.dat', retrieval.linear_scan, epsilon, verbose) \
            and test_retrieval('./tests/ls-1000-300-100.dat', retrieval.linear_scan, epsilon, verbose)
    else:
        return test_retrieval('t_ls.dat', retrieval.linear_scan, epsilon, verbose)

# Test Question 3
def test_Q3(verbose, longTests, epsilon):
    if longTests:
        return \
            test_median('./tests/median-01.dat', epsilon, verbose) \
            and test_median('./tests/median-02.dat', epsilon, verbose) \
            and test_median('./tests/median-03.dat', epsilon, verbose) \
            and test_median('./tests/median-04.dat', epsilon, verbose)
    else:
        return test_median('t_median.dat', epsilon, verbose)

# Test Question 4
def test_Q4(verbose, longTests, epsilon):
    if longTests:
        return \
            test_partition('./tests/partition-01.dat', epsilon, verbose) \
            and test_partition('./tests/partition-02.dat', epsilon, verbose) \
            and test_partition('./tests/partition-03.dat', epsilon, verbose) \
            and test_partition('./tests/partition-04.dat', epsilon, verbose)
    else:
        return test_partition('t_partition.dat', epsilon, verbose)

# Test Question 5
def test_Q5(verbose, longTests, epsilon):
    if longTests:
        return \
            test_build('./tests/back-1000-100-100.dat', verbose) \
            and test_build('./tests/back-1000-300-100.dat', verbose)
    else:
        return test_build('t_back.dat', verbose)

# Test Question 6
def test_Q6(verbose, longTests, epsilon):
    if longTests:
        return \
            test_retrieval('./tests/def-1000-100-100.dat', retrieval.defeatist_search, epsilon, verbose) \
            and test_retrieval('./tests/def-1000-300-100.dat', retrieval.defeatist_search, epsilon, verbose)
    else:
        return test_retrieval('t_def.dat', retrieval.defeatist_search, epsilon, verbose)

# Test Question 7
def test_Q7(verbose, longTests, epsilon):
    global count
    if longTests:
        result = \
            test_retrieval('./tests/back-1000-100-100.dat', retrieval.backtracking_search, epsilon, verbose) \
            and \
            test_retrieval('./tests/back-1000-300-100.dat', retrieval.backtracking_search, epsilon, verbose) \
            and \
            test_retrieval('./tests/back-1000-2-1000.dat', retrieval.backtracking_search, epsilon, verbose)

        if count > 15766:
            print(f"It seems that your backtracking_search_help() function is called too many times")
        elif count < 15766:
            print(f"It seems that your backtracking_search_help() function is called too few times")                
        return result
    else:
        result = test_retrieval('t_back.dat', retrieval.backtracking_search, epsilon, verbose)
        if count > 158:
            print(f"It seems that your backtracking_search_help() function is called too many times")
        elif count < 158:
            print(f"It seems that your backtracking_search_help() function is called too few times")                
        return result

verbose = True
longTests = True
epsilon = 0.00001

test_Q1(verbose, longTests, epsilon)
test_Q2(verbose, longTests, epsilon)
test_Q3(verbose, longTests, epsilon)
test_Q4(verbose, longTests, epsilon)
test_Q5(verbose, longTests, epsilon)
test_Q6(verbose, longTests, epsilon)
test_Q7(verbose, longTests, epsilon)

