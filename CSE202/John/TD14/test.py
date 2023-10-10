# -*- coding: utf-8 -*-

import random
import time
import math
from matplotlib import pyplot as plt


from WG import *

def dist(p1,p2):
    return (math.sqrt((p1[0]-p2[0])**2 + ((p1[1]-p2[1])**2)))

def dist_int(p1,p2):
    return int(dist(p1,p2))

def read_cities():
  cities=["Barcelona","Belgrade","Berlin","Brussels","Bucharest","Budapest","Copenhagen","Dublin","Hamburg","Istanbul","Kiev","London","Madrid","Milan","Moscow","Munich","Paris","Prague","Rome","Saint Petersbourg", "Sofia", "Stockholm", "Vienna", "Warsaw"]
  distances=[]
  with open("cities.txt") as f:
      content = f.readlines()
      distances = [x.strip().split() for x in content]
      #print(content)
  list_edges=[]    
  for j in range(0,len(cities)-1):
      for i in range(j):
          list_edges.append([cities[i],cities[j],int(distances[i][j])])
  #print(list_edges)        
  return WG(list_edges)
  #wg.display()    

def read_tsp_instance(instance_name):
    cities = []
    pos = []
    with open(instance_name+'.txt') as f:
        lines = f.readlines()
        for l in lines:
            node = l.strip().split()
            cities.append(int(node[0]))
            pos.append((int(node[1]),int(node[2])))
    list_edges = []
    for i in range(0, len(cities)-1):
        for j in range(i+1, len(cities)):
            list_edges.append([cities[i], cities[j], dist(pos[i],pos[j])])
    return WG(list_edges),pos

def check_edges(edges1, edges2):
    if len(edges1) != len(edges2):
        print('Failure. Extra or missing edges')
        return False
        
    for e in edges2:
        if not (e[0],e[1]) in edges1 and not (e[1],e[0]) in edges1:
            print('Failure. The edge ', e, ' should not be part of the selected edges.')
            return False
            
    print('Success !')
    return True


def tutorial_instance():  
    N= ['a', 'b', 'c', 'd', 'e', 'f', 'g']
    P= [(0,0),(0,2),(0,4),(1.5,5.5), (3,4),(3,2),(3,0)]
    L = []
    for i in range(len(N)):
        for j in range(i+1,len(N)):
            L.append([N[i],N[j], dist_int(P[i],P[j])])
            
    return WG(L)

def test1():
    print('Test 1: greedy_select_edges')
    wg =tutorial_instance()
    S = {('d', 'e'), ('b', 'c'), ('a', 'g'), ('a', 'b'), ('c', 'd'), ('f', 'g'), ('e', 'f')}
    R = wg.greedy_select_edges()
    print('Instance: Tutorial example')
    check_edges(S,R)
    
    wg = read_cities()
    S = {('Moscow', 'Saint Petersbourg'), ('Prague', 'Vienna'), ('Brussels', 'Paris'), ('Barcelona', 'Rome'), ('Bucharest', 'Istanbul'), ('Berlin', 'Prague'), ('Milan', 'Munich'), ('Barcelona', 'Madrid'), ('Brussels', 'London'), ('Kiev', 'Moscow'), ('Saint Petersbourg', 'Stockholm'), ('Berlin', 'Hamburg'), ('Copenhagen', 'Hamburg'), ('Dublin', 'London'), ('Copenhagen', 'Stockholm'), ('Bucharest', 'Sofia'), ('Belgrade', 'Budapest'), ('Belgrade', 'Sofia'), ('Munich', 'Paris'), ('Dublin', 'Kiev'), ('Budapest', 'Vienna'), ('Istanbul', 'Madrid'), ('Milan', 'Rome')}
    R = wg.greedy_select_edges()
    
    print('Instance: European cities')
    check_edges(S,R)


def test2():
    print('Test 2: greedy_min')
    wg =tutorial_instance()
    w, T = wg.greedy_min()
    print('Instance: Tutorial example')
    if w == 15:
        print('Success !')
    else:
        print('Failure. Your tour: ',(w,T))
        print("Should be: (15, ['d', 'e', 'f', 'g', 'a', 'b', 'c'])")
    
    wg = read_cities()
    w,T = wg.greedy_min()
    if w == 14427:
        print('Success !')
    else:
        print('Failure. Your tour: ',(w,T))
        print("Should be: (14427, ['Moscow', 'Saint Petersbourg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev'])")


def test3():
    print('Test 3: evaluate_flip')
    wg = tutorial_instance()
    T = ['a','b','e','d','c','f','g']
    
    print('Instance: Tutorial example')
    print('Circuit ', T)

    print('Evaluate flip (2,4)')
    g = wg.evaluate_flip(T,2,4) 
    if g == 2:
        print('Success !')
    else:
        print('Failure. Obtained ', g, ' but expected 2')

    print('Evaluate flip (2,5)')
    g = wg.evaluate_flip(T,2,5) 
    if g == -2:
        print('Success !')
    else:
        print('Failure. Obtained ', g, ' but expected -2')
        
    print('Evaluate flip (3,4)')
    g = wg.evaluate_flip(T,3,4) 
    if g == -1:
        print('Success !')
    else:
        print('Failure. Obtained ', g, ' but expected -1')


def test4():
    print('Test 4: find_best_opt2')
    
    wg = tutorial_instance()
    T = ['a','b','e','d','c','f','g']
    
    print('Instance: Tutorial example')
    print('Circuit ', T)
    flip,g = wg.find_best_opt2(T)
    if g == 2:
        print('Success !')
    else:
        print('Failure. Obtained ', (flip,g), ' but expected a flip (2,4) of gain 2')
    
    
    print('Instance: European cities')
    wg = read_cities()
    T = ['Moscow', 'Saint Petersbourg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev']
    print('Circuit ', T)
    
    flip,g = wg.find_best_opt2(T)
    if g == 784:
        print('Success !')
    else:
        print('Failure. Obtained ', (flip,g), ' but expected a flip (13,18) of gain 2')

def test5():
    print('Test 5: opt_2')
    wg = tutorial_instance()
    T = ['a','b','e','d','c','f','g']
    w = wg.eval_circuit(T)
    
    print('Instance: Tutorial example')
    print('Circuit ', T)
    w,L = wg.opt_2(w,T)
    #print(w,L)
    if w == 15:
        print('Success !')
    else:
        print('Failure. Obtained ', (w,L), " but expected (15, ['a','b','c','d','e','f','g'])")
    
    
    print('Instance: European cities')
    wg = read_cities()
    T = ['Moscow', 'Saint Petersbourg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev']
    w = wg.eval_circuit(T)    
    print('Circuit ', T)
    
    w,L = wg.opt_2(w,T)
    #print(w,L)
    if w == 13643:
        print('Success !')
    else:
        print('Failure. Obtained ', (w,L), " but expected (13643,['Moscow', 'Saint Petersbourg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Munich', 'Milan', 'Rome', 'Barcelona', 'Madrid', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev'])")


def test6():
    print('Test 6: neighborhood_search_opt2')
    wg = tutorial_instance()
    T = ['d','e','b','a','f','g','c']
    w = wg.eval_circuit(T)
    print('Instance: Tutorial example')
    print('Circuit ', T)
    w,L = wg.neighborhood_search_opt2(w,T)
    #print(w,L)
    if w == 15:
        print('Success !')
    else:
        print('Failure. Obtained ', (w,L), " but expected (15, ['d', 'e', 'f', 'g', 'a', 'b', 'c'])")
 
    print('Instance: European cities')
    wg = read_cities()
    T = ['Moscow', 'Saint Petersbourg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Madrid', 'Barcelona', 'Rome', 'Milan', 'Munich', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev']
    w = wg.eval_circuit(T)    
    print('Circuit ', T)
    
    w,L = wg.neighborhood_search_opt2(w,T)
    #print(w,L)
    if w == 11749:
        print('Success !')
    else:
        print('Failure. Obtained ', (w,L), " but expected (11749,['Moscow', 'Saint Petersbourg', 'Stockholm', 'Copenhagen', 'Hamburg', 'Berlin', 'Prague', 'Vienna', 'Budapest', 'Belgrade', 'Sofia', 'Bucharest', 'Istanbul', 'Munich', 'Milan', 'Rome', 'Barcelona', 'Madrid', 'Paris', 'Brussels', 'London', 'Dublin', 'Kiev'])")


def randomWG(n):
    L=[]
    for i in range(n):
      #L.append([i,i,0])
      for j in range(i+1,n):
          L.append([i,j,random.random()])
    return WG(L)

def random_euclidian(n):
    r = 1000
    pos = [(random.randint(0,r), random.randint(0,r)) for _ in range(n)]
    
    L = []    
    for i in range(n-1):
        for j in range(i+1, n):
            L.append([i,j, dist(pos[i],pos[j])])

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
    topt2r  =[]
    topt2g = []
    
    for n in x:
        wg = random_euclidian(n)
        
        start = time.process_time()
        s = wg.greedy_min()
        tgreedy.append(time.process_time() - start)
        ygreedy.append(s[0])
        
        start = time.process_time()
        s = wg.neighborhood_search_opt2(s[0],s[1])
        topt2g.append(time.process_time() - start)
        yopt2g.append(s[0])
        
        
        avgs = 0
        mins = math.inf
        
        avgr = 0
        minr = math.inf
        for _ in range(numtrial):
            
            start = time.process_time()
            T,w = wg.random_circuit()
            avgr += time.process_time() - start
            if w < minr:
                minr = w
            
            start = time.process_time()
            s = wg.neighborhood_search_opt2(w,T)
            avgs += time.process_time() - start
            if s[0] < mins:
                mins = s[0]
        topt2r.append(avgs/numtrial)
        yopt2r.append(mins)
        
        trand.append(avgr/numtrial)
        yrand.append(minr)
    
    plt.plot(x, yrand, color='red', label='rand')
    plt.plot(x, ygreedy, color = 'blue', label='greedy')
    plt.plot(x, yopt2g, color='magenta', label='greedy opt2')
    plt.plot(x, yopt2r, color='green', label='rand opt2')
    plt.legend(loc='upper left')
    plt.title('Comparison solution quality')
    plt.show()

    plt.plot(x, trand, color='red', label='rand')
    plt.plot(x, tgreedy, color = 'blue', label='greedy')
    plt.plot(x, topt2g, color='magenta', label='greedy opt2')
    plt.plot(x, topt2r, color='green', label='rand opt2')
    plt.legend(loc='upper left')
    plt.title('Comparison computational time')    
    plt.show()
        
        



def get_ordered_coordinates(T, pos):
    x = []
    y = []
    for t in T:
        p = pos[t-1]
        x.append(p[0])
        y.append(p[1])
    x.append(x[0])
    y.append(y[0])
    return x,y
    
def run_drill_instance():
    wg, pos = read_tsp_instance('a280')
    s = wg.greedy_min()
    #print(s[1])
    x,y = get_ordered_coordinates(s[1], pos)
    plt.plot(x,y, color='blue',marker=".")
    plt.title('cost '+str(s[0]))
    plt.show()
    
    s2 = wg.neighborhood_search_opt2(s[0],s[1])
    #print(s2)
    print(wg.eval_circuit(s2[1]))
    
    x,y = get_ordered_coordinates(s2[1], pos)
    plt.plot(x,y, color='red',marker=".")
    plt.title('cost '+str(s2[0]))
    plt.show()
    
    print('min tree bound:',wg.weight_min_tree(list(wg.adj.keys())))
    
def run_us_instance():
    wg, pos = read_tsp_instance('att48')
    s = wg.greedy_min()
    #print(s)
    x,y = get_ordered_coordinates(s[1], pos)
    plt.plot(x,y, color='blue',marker=".")
    plt.title('cost '+str(s[0]))
    plt.show()
    
    s2 = wg.neighborhood_search_opt2(s[0],s[1])
    #print(s2)
    print(wg.eval_circuit(s2[1]))
    
    x,y = get_ordered_coordinates(s2[1], pos)
    plt.plot(x,y, color='red',marker=".")
    plt.title('cost '+str(s2[0]))
    plt.show()
    
    print('min tree bound:',wg.weight_min_tree(list(wg.adj.keys())))
    
def run_eu_instance(): 
  wg=read_cities()
  
  
  s =wg.greedy_min()
  print('greedy ', s)
  print('2-opt greedy ', wg.neighborhood_search_opt2(s[0],s[1]))
  print('min tree bound', wg.weight_min_tree(list(wg.adj.keys())))
  
  
  





test1()
test2()
test3()
test4()
test5()
test6()

compare_approx()
run_eu_instance()
run_us_instance()
run_drill_instance()
