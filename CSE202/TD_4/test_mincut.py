import math

import MultiGraph as sol

# L_tutorial = [8, [['a', 'c', 1], ['a', 'g', 1], ['a', 'd', 1], ['a', 'b', 1], ['g', 'c', 2], ['g', 'd', 1], ['d', 'c', 1], ['b', 'e', 1], ['b', 'h', 1], ['b', 'f', 2], ['f', 'h', 1], ['e', 'h', 1], ['e', 'f', 1], ['e', 'd', 1], ['g', 'h', 1]]]
# L_tutorial_mincut = [3, ['a', 'c', 'd', 'g']]

def two_clique_graph(n): 
# produces graph on 2*n vertices with two cliques (a first clique for vertices of label in [1..n], a second clique
# for vertices with labels in [n+1..2n]). The two cliques are connected by n-2 edges, and thus the mincut has
# size n-2, and is uniquely realized as the cut into S=[1..n] and complement(S)=[n+1..2n] 
    list_edges = []
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            list_edges.append([i, j, 1])
            list_edges.append([2 * n - i + 1, 2 * n - j + 1, 1])
    for i in range(1, n - 1):
        list_edges.append([i, 2 * n - i + 1, 1])
    return [2 * n, list_edges]

def mincut_brute(m):
    n = len(m.adj)
    best = [math.inf]
    for i in range(1, 2 ** n - 1, 2):
        cut = m.cutsize(i)
        if cut[0] < best[0]:
            best = cut
    return best

def test_mincut_brute(n = 9):
    print()
    print("Testing mincut_brute")
    G = two_clique_graph(n)
    mincut_brute(sol.MultiGraph(G))

def same_graph(g1, g2):
    if g1.adj != g2.adj:
        print("     The adjacencies are not correct.")
        return
    if g1.deg != g2.deg:
        print("     The degrees are not correct.")
        return
    print("     The graph is correct.")



def test_contract():
    print("\nTesting 'contract'")
    Lt = [5, [['a', 'b', 1], ['a', 'c', 1], ['a', 'e', 1], ['b', 'c', 1], ['b', 'e', 2], ['c', 'e', 1], ['c', 'd', 1]]]
    Lt_cont_eb = [4, [['a', 'e', 2], ['a', 'c', 1], ['c', 'e', 2], ['c', 'd', 1]]]
    Lt_cont_cd = [4, [['a', 'b', 1], ['a', 'c', 1], ['a', 'e', 1], ['b', 'c', 1], ['b', 'e', 2], ['c', 'e', 1]]]
    m = sol.MultiGraph(Lt)
    m2 = sol.MultiGraph(Lt_cont_eb)
    # print("Multigraph middle of Figure 3")
    #m.display()
    print("** Contraction of {e, b}. Should obtain the multigraph on the left of Figure 3 (if no error message then result is correct)")
    m.contract('e', 'b')
    same_graph(m, m2)
    #m.display()
    m = sol.MultiGraph(Lt)
    m2 = sol.MultiGraph(Lt_cont_cd)
    print("** Contraction of {c, d}. Should obtain the multigraph on the right of Figure 3 (if no error message then result is correct)")
    m.contract('c', 'd')
    #m.display()
    same_graph(m, m2)


  
def test_random_element():
    print()   
    print("Testing 'random_element'")
    data = {'a': 2, 'b': 1, 'c': 4}
    if sol.random_element(data) is None:
        print("** Skipping this test (method not implemented).")
        return
    na = nb = nc = 0
    ntrials = 50000
    actualTrials = 0
    for _ in range(ntrials):
        u = sol.random_element(data)
        if u == 'a':
            na += 1
        elif u == 'b':
            nb += 1
        elif u == 'c':
            nc += 1
        else:
            break
        actualTrials += 1
    if actualTrials != ntrials:
        print("     Your method returned an unknown value.")
        return
    print("  Frequency of a (should be close to 0.28): " + str(na / ntrials))
    print("  Frequency of b (should be close to 0.14): " + str(nb / ntrials))
    print("  Frequency of c (should be close to 0.57): " + str(nc / ntrials))
    err = 0.05
    if not (abs(na / ntrials - 2 / 7) <= err and abs(nb / ntrials - 1 / 7) <= err and abs(nc / ntrials - 4 / 7) <= err):
        print("    Your code seems to not have the right frequencies.")
    else:
        print("    Your code seems to have the right frequencies.")



def test_random_edge():
    print()
    print("Testing 'random_edge'")
    L_graph = [3, [['a', 'b', 1], ['a', 'c', 2], ['b', 'c', 3]]]
    m = sol.MultiGraph(L_graph)
    if m.random_edge() is None:
        print("** Skipping this test (method not implemented).")
        return
    nab = nac = nbc = 0
    ntrials = 50000
    for _ in range(ntrials):
        [u, v] = m.random_edge()
        if (u == 'a' and v == 'b') or  (u == 'b' and v == 'a'):
            nab += 1
        if (u == 'a' and v == 'c') or  (u == 'c' and v == 'a'):
            nac += 1
        if (u == 'b' and v == 'c') or  (u == 'c' and v == 'b'):
            nbc += 1
    print("  Frequency of {a, b} (should be close to 0.166): " + str(nab / ntrials))
    print("  Frequency of {a, c} (should be close to 0.333): " + str(nac / ntrials))
    print("  Frequency of {b, c} (should be close to 0.5): " + str(nbc / ntrials))
    err = 0.05
    if not (abs(nab / ntrials - 1 / 6) <= err and abs(nac / ntrials - 1 / 3) <= err and abs(nbc / ntrials - 1 / 2) <= err):
        print("    Your code seems to not have the right frequencies.")
    else:
        print("    Your code seems to have the right frequencies.")



def test_random_cut():
    print()   
    print("Testing 'random_cut'")    
    L_graph = [4, [['a', 'b', 1], ['b', 'c', 1], ['c', 'd', 1], ['a', 'd', 2]]]
    m = sol.MultiGraph(L_graph)
    if sol.random_cut(m) is None:
        print("** Skipping this test (method not implemented).")
        return
    nab = nac = nad = na = nb = nc = nd = 0 
    ntrials = 10000
    for _ in range(ntrials):
        m = sol.MultiGraph(L_graph)
        [c, L] = sol.random_cut(m)
        if c == 3 and (len(L) == 1 and 'a' in L) or (len(L) == 3 and 'a' not in L):
            na += 1
        elif c == 2 and ((len(L) == 1 and 'b' in L) or (len(L) == 3 and 'b' not in L)):
            nb += 1
        elif c == 2 and ((len(L) == 1 and 'c' in L) or (len(L) == 3 and 'c' not in L)):
            nc += 1
        elif c == 3 and ((len(L) == 1 and 'd' in L) or (len(L) == 3 and 'd' not in L)):
            nd += 1
        elif c == 3 and len(L) == 2 and (('a' in L and 'b' in L) or ('c' in L and 'd' in L)):
            nab += 1
        elif c == 2 and len(L) == 2 and (('a' in L and 'd' in L) or ('b' in L and 'c' in L)):
            nad += 1
        else:
            nac += 1
    print("  Frequency of {a} U {b, c, d} (should be close to 0.1): " + str(na / ntrials))
    print("  Frequency of {b} U {a, c, d} (should be close to 0.233): " + str(nb / ntrials))
    print("  Frequency of {c} U {a, c, d} (should be close to 0.233): " + str(nc / ntrials))
    print("  Frequency of {d} U {a, b, c} (should be close to 0.1): " + str(nd / ntrials))
    print("  Frequency of {a, b} U {c, d} (should be close to 0.1): " + str(nab / ntrials))
    print("  Frequency of {a, c} U {b, d} (should be 0): " + str(nac / ntrials))
    print("  Frequency of {a, d} U {b, c} (should be close to 0.233): " + str(nad / ntrials))
    err = 0.05
    if not (abs(na / ntrials - 0.1) <= err and abs(nb / ntrials - 0.233) <= err and abs(nc / ntrials - 0.233) <= err and \
            abs(nd / ntrials - 0.1) <= err and abs(nab / ntrials - 0.1) <= err and abs(nac / ntrials) <= err and \
            abs(nad / ntrials - 0.233) <= err):
        print("    Your code seems to not have the right frequencies.")
    else:
        print("    Your code seems to have the right frequencies.")



def test_mincut_karger():
    print()
    print("Testing 'randomized_karger'")
    if sol.mincut_karger(two_clique_graph(15), 0.1) is None:
        print("** Skipping this test (method not implemented).")
        return
    for i in range(15, 22): 
        print("** Two-clique graph with " + str(2 * i) + " vertices and mincut size " + str(i - 2) + ".")
        L = two_clique_graph(i)
        print("     " , sol.mincut_karger(L, 0.1))
    
test_contract()
test_random_element()
test_random_edge()
test_random_cut()

test_mincut_karger()
test_mincut_brute()
