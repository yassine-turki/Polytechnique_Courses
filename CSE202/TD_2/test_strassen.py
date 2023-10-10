# -*- coding: utf-8 -*-

import strassen(2) as strassen
import networkx as nx # to plot graphs
import numpy as np # to manipulate matrices
import matplotlib.pyplot as plt # to make several figures

grading_mode = False


A1 = [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]
A2 = [[2,1,3,7],[-2,1,0,3],[-3,-1,1,1],[0,0,0,1]]
Ares = [[2, 1, 3, 7], [-2, 1, 0, 3], [-3, -1, 1, 1], [0, 0, 0, 1]]
A2bool = [[1,1,1,1],[0,1,0,1],[0,0,1,1],[0,0,0,1]]

B1 = [[2,0,1,0],[0,0,1,2],[-1,2,0,10],[0,2,3,0]]
B2 = [[2,1,3,7],[-2,1,0,3],[-3,-1,1,1],[0,0,0,1]]
Bres = [[1, 1, 7, 15], [-3, -1, 1, 3], [-6, 1, -3, 9], [-13, -1, 3, 9]]
B1bool = [[1,0,1,0],[0,0,1,1],[0,1,0,1],[0,1,1,0]]
B2bool = [[1,1,1,1],[0,1,0,1],[0,0,1,1],[0,0,0,1]]

G1 = [[0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]]
G1tc = [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

G2 = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
G2tc = [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

def equal_matrix(A1,A2):
    n = len(A1)
    m = len(A2)
    if (m != n):
        return False
    for i in range(n):
        for j in range(n):
            if (A1[i][j]!=A2[i][j]):
                return False
    return True

def check_mult_matrix(fn,A1, A2, res):
    tmp = fn(A1, A2)
    if not equal_matrix(tmp ,res):
        print("your product of {} and {} returned {} instead of {}".format(str(A1), str(A2), str(tmp), str(res)))
        assert not grading_mode
        
def check_cost_mult_matrix(fn,n,res):
    tmp = fn(n)
    if (tmp != res):
        print("your cost of {} returned {} instead of {}".format(str(n), str(tmp), str(res)))
        assert not grading_mode
        
def check_convert_01(fn,A,res):
    return equal_matrix(fn(A),res)

def check_transitive_closure(fn,A,res):
    return equal_matrix(fn(A),res)
        
def test6():
    if strassen.mult_matrix([[0]], [[0]]) is None:
        print("skipping mult_matrix (unimplemeneted)")
        assert not grading_mode
        return
    check_mult_matrix(strassen.mult_matrix, A1, A2, Ares)
    check_mult_matrix(strassen.mult_matrix, B1, B2, Bres)
    print("mult_matrix done.")       
        
def test7():
    if strassen.cost_mult_matrix(1) is None:
        print("skipping cost_mult_matrix (unimplemeneted)")
        assert not grading_mode
        return
    res = [0, 2, 16, 54, 128, 250, 432, 686, 1024, 1458, 2000, 2662, 3456, 4394, 5488, 6750, 8192, 9826, 11664, 13718]
    for i in range(20):
        check_cost_mult_matrix(strassen.cost_mult_matrix,i,res[i])
    print("cost_mult_matrix done.")   

def test8():
    if strassen.strassen([[0]], [[0]]) is None:
        print("skipping strassen (unimplemeneted)")
        assert not grading_mode
        return
    check_mult_matrix(strassen.strassen, A1, A2, Ares)
    check_mult_matrix(strassen.strassen, B1, B2, Bres)
    print("strassen done.")       
        
def test9():
    if strassen.cost_strassen(1) is None:
        print("skipping cost_strassen (unimplemeneted)")
        assert not grading_mode
        return
    res = [1, 25, 247, 2017, 15271, 111505, 798967, 5666497, 39960391, 280902385, 1971035287, 13816121377, 96788347111, 677820419665, 4745950897207, 33226488118657, 232604744183431, 1628310518695345, 11398482868512727, 79790617030170337]
    for i in range(20):
        check_cost_mult_matrix(strassen.cost_strassen,i,res[i])
    print("cost_strassen done.")   

def test10():
    if strassen.convert_01([[0]]) is None:
        print("skipping convert_01 (unimplemeneted)")
        assert not grading_mode
        return
    check_convert_01(strassen.convert_01, A2, A2bool)
    check_convert_01(strassen.convert_01, B1, B1bool)
    check_convert_01(strassen.convert_01, B2, B2bool)
    
    print("convert_bool done.")      
  
def test11():
    if strassen.transitive_closure([[0]]) is None:
        print("skipping transitive_closure (unimplemeneted)")
        assert not grading_mode
        return
    check_transitive_closure(strassen.transitive_closure, G1, G1tc)
    GG1=np.array(G1)
    g1 = nx.from_numpy_matrix(GG1)
    plt.figure(1)
    plt.title('Graph G_1')
    nx.draw(g1, with_labels = True)
    plt.savefig("graph1.png")
    
    GG1tc=np.array(G1tc)
    g1tc = nx.from_numpy_matrix(GG1tc)
    plt.figure(2)
    plt.title('Transitive closure of G_1')
    nx.draw(g1tc, with_labels = True)
 
    Your1tc=np.array(strassen.transitive_closure(G1))
    your1tc = nx.from_numpy_matrix(Your1tc)
    plt.figure(3)
    plt.title('Your transitive closure of G_1')
    nx.draw(your1tc, with_labels = True)   
 
    check_transitive_closure(strassen.transitive_closure, G2, G2tc)
    GG2=np.array(G2)
    g2 = nx.from_numpy_matrix(GG2)
    plt.figure(4)
    plt.title('Graph G_2')
    nx.draw(g2, with_labels = True)
    
    GG2tc=np.array(G2tc)
    g2tc = nx.from_numpy_matrix(GG2tc)
    plt.figure(5)
    plt.title('Transitive closure of G_2')
    nx.draw(g2tc, with_labels = True)   
    
    Your2tc=np.array(strassen.transitive_closure(G2))
    your2tc = nx.from_numpy_matrix(Your2tc)
    plt.figure(6)
    plt.title('Your transitive closure of G_2')
    nx.draw(your2tc, with_labels = True)  
 
    print("transitive_closure done.")     
  
test6()
test7()
test8()
test9()
test10()
test11()


