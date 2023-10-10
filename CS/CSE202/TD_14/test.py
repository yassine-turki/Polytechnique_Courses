import random
import time
import math
from matplotlib import pyplot as plt

from WG import *

############
## Colors ##
############

Black  = "\033[0m"
Red    = "\033[31m"
Green  = "\033[32m"
Yellow = "\033[33m"
Blue   = "\033[0m"

#################
## Auxiliaries ##
#################

def dist(p1, p2):
    return math.sqrt((p1[0] - p2[0]) ** 2 + ((p1[1] - p2[1]) ** 2))

def dist_int(p1, p2):
    return int(dist(p1, p2))

def read_cities():
  cities = ["Barcelona", "Belgrade", "Berlin", "Brussels", "Bucharest", "Budapest", "Copenhagen", "Dublin", "Hamburg", "Istanbul", "Kiev", "London", "Madrid", "Milan", "Moscow", "Munich", "Paris", "Prague", "Rome", "Saint Petersburg", "Sofia", "Stockholm", "Vienna", "Warsaw"]
  distances = []
  with open("cities.txt") as f:
      content = f.readlines()
      distances = [x.strip().split() for x in content]
  list_edges = []
  for j in range(0, len(cities) - 1):
      for i in range(j):
          list_edges.append([cities[i], cities[j], int(distances[i][j])])
  return WG(list_edges)

def read_tsp_instance(instance_name):
    cities = []
    pos = []
    with open(instance_name + '.txt') as f:
        lines = f.readlines()
        for l in lines:
            node = l.strip().split()
            cities.append(int(node[0]))
            pos.append((int(node[1]), int(node[2])))
    list_edges = []
    for i in range(0, len(cities) - 1):
        for j in range(i + 1, len(cities)):
            list_edges.append([cities[i], cities[j], dist(pos[i],pos[j])])
    return (WG(list_edges), pos)

def check_edges(edges1, edges2):
    if len(edges1) != len(edges2):
        print(Red + '    Failure!' + Black + ' Additional or missing edges.')
        return False

    for e in edges2:
        if not (e[0], e[1]) in edges1 and not (e[1], e[0]) in edges1:
            print(Red + '    Failure!' + Black + ' The edge ', e, ' should not be part of the selected edges.')
            return False

    print(Green + '    Success!' + Black)
    return True


def tutorial_instance():
    N = ['a', 'b', 'c', 'd', 'e', 'f', 'g']
    P = [(0, 0), (0, 2), (0, 4), (1.5, 5.5), (3, 4), (3, 2), (3, 0)]
    L = []
    for i in range(len(N)):
        for j in range(i + 1, len(N)):
            L.append([N[i], N[j], dist_int(P[i], P[j])])

    return WG(L)

###########
## Tests ##
###########

def test1():
    print('Testing' + Blue + ' greedily_select_edges' + Black + ':')
    wg = tutorial_instance()
    S = {('d', 'e'), ('b', 'c'), ('a', 'g'), ('a', 'b'), ('c', 'd'), ('f', 'g'), ('e', 'f')}
    R = wg.greedily_select_edges()
    if(R is None):
        print(Yellow + '  Skipping.' + Black + ' Not implemented.')
        return

    print('  Instance: Tutorial example')
    check_edges(S,R)

    wg = read_cities()
    S = {('Moscow', 'Saint Petersburg'), ('Prague', 'Vienna'), ('Brussels', 'Paris'), ('Barcelona', 'Rome'), ('Bucharest', 'Istanbul'), ('Berlin', 'Prague'), ('Milan', 'Munich'), ('Barcelona', 'Madrid'), ('Brussels', 'London'), ('Kiev', 'Moscow'), ('Saint Petersburg', 'Stockholm'), ('Berlin', 'Hamburg'), ('Copenhagen', 'Hamburg'), ('Dublin', 'London'), ('Copenhagen', 'Stockholm'), ('Bucharest', 'Sofia'), ('Belgrade', 'Budapest'), ('Belgrade', 'Sofia'), ('Munich', 'Paris'), ('Dublin', 'Kiev'), ('Budapest', 'Vienna'), ('Istanbul', 'Madrid'), ('Milan', 'Rome')}
    R = wg.greedily_select_edges()

    print('  Instance: European cities')
    check_edges(S,R)

def test2():
    print('\nTesting' + Blue + ' build_cycle_from_edges' + Black + '.')
    wg = tutorial_instance()
    R = wg.greedy_min()
    if(R is None):
        print(Yellow + '  Skipping.' + Black + ' Not implemented.')
        return

    (w, T) = R
    print('  Instance: Tutorial example')
    if w == 15:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Your tour: ', (w, T))
        print("    Expected: (15, ['d', 'e', 'f', 'g', 'a', 'b', 'c'])")
        return

    wg = read_cities()
    (w, T) = wg.greedy_min()
    print('  Instance: European cities')
    if w == 14427:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Your tour: ', (w, T))
        print("    Expected: (14427, ['Moscow', 'Saint Petersburg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev'])")

def test3():
    print('\nTesting' + Blue + ' evaluate_flip' + Black + '.')
    wg = tutorial_instance()
    T = ['a', 'b', 'e', 'd', 'c', 'f', 'g']
    g = wg.evaluate_flip(T, 2, 4)
    if(g is None):
        print(Yellow + '  Skipping.' + Black + ' Not implemented.')
        return

    print('  Instance: Tutorial example')
    print('   Using cycle ' + Yellow + str(T) + Black + '.')
    print('   Flipping ' + Yellow + '(2, 4)' + Black + '.')
    if g == 2:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, g, Black + 'but expected ' + Yellow + '2' + Black + '.')
        return

    print('   Flipping ' + Yellow + '(2, 5)' + Black)
    g = wg.evaluate_flip(T, 2, 5)
    if g == -2:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, g, Black + 'but expected ' + Yellow + '-2' + Black + '.')
        return

    print('   Flipping ' + Yellow + '(3, 4)' + Black)
    g = wg.evaluate_flip(T, 3, 4)
    if g == -1:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, g, Black + 'but expected ' + Yellow + '-1' + Black + '.')

def test4():
    print('\nTesting ' + Blue + 'find_best_opt2' + Black + '.')

    wg = tutorial_instance()
    T = ['a','b','e','d','c','f','g']
    R = wg.find_best_opt2(T)
    if(R is None):
        print(Yellow + '  Skipping.' + Black + ' Not implemented.')
        return

    print('  Instance: Tutorial example')
    print('   Using cycle ' + Yellow + str(T) + Black + '.')
    (flip, g) = R
    if g == 2:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, (flip, g), Black + 'but expected a flip of ' + Yellow + '(2, 4)' + Black + ' gaining ' + Yellow + '2' + Black + '.')
        return

    print('  Instance: European cities')
    wg = read_cities()
    T = ['Moscow', 'Saint Petersburg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev']
    print('   Using cycle ' + Yellow + str(T) + Black + '.')

    flip,g = wg.find_best_opt2(T)
    if g == 784:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, (flip, g), Black + 'but expected a flip of ' + Yellow + '(13, 18)' + Black + ' gaining ' + Yellow + '2' + Black + '.')

def test5():
    print('\nTesting ' + Blue + 'opt_2' + Black + '.')
    wg = tutorial_instance()
    T = ['a', 'b', 'e', 'd', 'c', 'f', 'g']
    w = wg.eval_cycle(T)
    R = wg.opt_2(w, T)
    if(R is None):
        print(Yellow + '  Skipping.' + Black + ' Not implemented.')
        return

    (w, L) = R
    print('  Instance: Tutorial example')
    print('   Using cycle ' + Yellow + str(T) + Black + '.')
    if w == 15:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, (w, L), Black + 'but expected  ' + Yellow + "(15, ['a', 'b', 'c', 'd', 'e', 'f', 'g'])" + Black + '.')
        return

    print('  Instance: European cities')
    wg = read_cities()
    T = ['Moscow', 'Saint Petersburg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev']
    w = wg.eval_cycle(T)
    print('   Using cycle ' + Yellow + str(T) + Black + '.')

    (w, L) = wg.opt_2(w,T)
    if w == 13643:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, (w, L), Black + 'but expected  ' + Yellow + "(13643, ['Moscow', 'Saint Petersburg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Munich', 'Milan', 'Rome', 'Barcelona', 'Madrid', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev'])" + Black + '.')

def test6():
    print('\nTesting ' + Blue + 'neighborhood_search_opt2' + Black + '.')
    wg = tutorial_instance()
    T = ['d', 'e', 'b', 'a', 'f', 'g', 'c']
    w = wg.eval_cycle(T)
    R = wg.neighborhood_search_opt2(w, T)
    if(R is None):
        print(Yellow + '  Skipping.' + Black + ' Not implemented.')
        return

    print('  Instance: Tutorial example')
    print('   Using cycle ' + Yellow + str(T) + Black + '.')
    (w, L) = R
    if w == 15:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, (w, L), Black + 'but expected  ' + Yellow + "(15, ['d', 'e', 'f', 'g', 'a', 'b', 'c'])" + Black + '.')
        return

    print('  Instance: European cities')
    wg = read_cities()
    T = ['Moscow', 'Saint Petersburg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev']
    w = wg.eval_cycle(T)
    print('   Using cycle ' + Yellow + str(T) + Black + '.')

    (w, L) = wg.neighborhood_search_opt2(w, T)
    if w == 11749:
        print(Green + '    Success!' + Black)
    else:
        print(Red + '    Failure!' + Black + ' Obtained' + Yellow, (w, L), Black + 'but expected  ' + Yellow + "(11749, ['Moscow', 'Saint Petersburg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Munich', 'Milan', 'Rome', 'Barcelona', 'Madrid', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev'])" + Black + '.')

###############
## Fun Stuff ##
###############

## Auxiliaries

def randomWG(n):
    L = []
    for i in range(n):
      for j in range(i + 1, n):
          L.append([i, j, random.random()])
    return WG(L)

def random_euclidian(n):
    r = 1000
    pos = [(random.randint(0, r), random.randint(0, r)) for _ in range(n)]

    L = []
    for i in range(n - 1):
        for j in range(i + 1, n):
            L.append([i, j, dist(pos[i], pos[j])])

    return WG(L)

def compare_approx():
    maxn = 50
    minn = 5
    numtrial = 5

    x = [n for n in range(minn, maxn)]

    yrand = []
    ygreedy = []
    yopt2r = []
    yopt2g = []

    trand = []
    tgreedy = []
    topt2r =[]
    topt2g = []

    for n in x:
        wg = random_euclidian(n)

        start = time.process_time()
        s = wg.greedy_min()
        tgreedy.append(time.process_time() - start)
        ygreedy.append(s[0])

        start = time.process_time()
        s = wg.neighborhood_search_opt2(s[0], s[1])
        topt2g.append(time.process_time() - start)
        yopt2g.append(s[0])


        avgs = 0
        mins = math.inf

        avgr = 0
        minr = math.inf
        for _ in range(numtrial):

            start = time.process_time()
            (T, w) = wg.random_cycle()
            avgr += time.process_time() - start
            if w < minr:
                minr = w

            start = time.process_time()
            s = wg.neighborhood_search_opt2(w, T)
            avgs += time.process_time() - start
            if s[0] < mins:
                mins = s[0]
        topt2r.append(avgs / numtrial)
        yopt2r.append(mins)

        trand.append(avgr / numtrial)
        yrand.append(minr)

    plt.plot(x, yrand, color = 'red', label = 'rand')
    plt.plot(x, ygreedy, color = 'blue', label = 'greedy')
    plt.plot(x, yopt2g, color = 'magenta', label = 'greedy opt2')
    plt.plot(x, yopt2r, color = 'green', label = 'rand opt2')
    plt.legend(loc = 'upper left')
    plt.title('Comparison solution quality')
    plt.xlabel('instance size')
    plt.ylabel('average solution quality')
    plt.show()

    plt.plot(x, trand, color = 'red', label = 'rand')
    plt.plot(x, tgreedy, color  =  'blue', label = 'greedy')
    plt.plot(x, topt2g, color = 'magenta', label = 'greedy opt2')
    plt.plot(x, topt2r, color = 'green', label = 'rand opt2')
    plt.legend(loc = 'upper left')
    plt.title('Comparison computational time')
    plt.xlabel('instance size')
    plt.ylabel('average time')
    plt.show()

def get_ordered_coordinates(T, pos):
    x = []
    y = []
    for t in T:
        p = pos[t - 1]
        x.append(p[0])
        y.append(p[1])
    x.append(x[0])
    y.append(y[0])
    return x, y

## Tests

def run_drill_instance():
    (wg, pos) = read_tsp_instance('a280')
    s = wg.greedy_min()
    (x, y) = get_ordered_coordinates(s[1], pos)
    plt.plot(x, y, color = 'blue', marker = ".")
    plt.title('cost ' + str(s[0]))
    plt.show()

    s2 = wg.neighborhood_search_opt2(s[0], s[1])
    print(wg.eval_cycle(s2[1]))

    (x, y) = get_ordered_coordinates(s2[1], pos)
    plt.plot(x, y, color = 'red', marker = ".")
    plt.title('cost ' + str(s2[0]))
    plt.show()

    print('min tree bound:', wg.weight_min_tree(list(wg.adj.keys())))

def run_us_instance():
    (wg, pos) = read_tsp_instance('att48')
    s = wg.greedy_min()
    (x, y) = get_ordered_coordinates(s[1], pos)
    plt.plot(x, y, color = 'blue', marker = ".")
    plt.title('cost ' + str(s[0]))
    plt.show()

    s2 = wg.neighborhood_search_opt2(s[0], s[1])
    print(wg.eval_cycle(s2[1]))

    (x, y) = get_ordered_coordinates(s2[1], pos)
    plt.plot(x, y, color = 'red', marker = ".")
    plt.title('cost ' + str(s2[0]))
    plt.show()

    print('min tree bound:', wg.weight_min_tree(list(wg.adj.keys())))

def run_eu_instance():
  wg = read_cities()
  s = wg.greedy_min()
  print('greedy ', s)
  print('2-opt greedy ', wg.neighborhood_search_opt2(s[0], s[1]))
  print('min tree bound', wg.weight_min_tree(list(wg.adj.keys())))

###############
## Run Tests ##
###############

test1()
test2()
test3()
test4()
test5()
#test6()

# compare_approx()
# run_eu_instance()
# run_us_instance()
# run_drill_instance()
