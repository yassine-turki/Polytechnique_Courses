# -*- coding: utf-8 -*-

from rw import *

L_tutorial=[[1,2,3],[0,2],[0,3,1],[0,2]]
g=Graph(L_tutorial) # graph of Figure 1

def test_random_neighbour():
    N=50000
    n0=0; n1=0; n3=0
    for i in range(N):
        j=g.random_neighbour(2)
        if j==0: 
            n0+=1
        elif j==1:
            n1+=1
        elif j==3:
            n3+=1
        else: 
            print("Error: should not find ",j," as neighbour of 1")
    print("Neighbours of 2:")
    print("Frequency of 0 (should be close to 0.33): ",n0/N)
    print("Frequency of 1 (should be close to 0.33): ",n1/N)
    print("Frequency of 3 (should be close to 0.33): ",n3/N)
    print("")    
    
    n0=0; n2=0
    for i in range(N):
        j=g.random_neighbour(3)
        if j==0: 
            n0+=1
        elif j==2:
            n2+=1
        else: 
            print("Error: should not find ",j," as neighbour of 3")
    print("Neighbours of 3:")
    print("Frequency of 0 (should be close to 0.5): ",n0/N)
    print("Frequency of 2 (should be close to 0.5): ",n2/N)
    


def test_random_walk():
    n010=0; n012=0; n030=0; n032=0; n020=0; n021=0; n023=0
    N=100000
    for i in range(N):
        L=g.random_walk(2)
        if L==[0,1,0]:
            n010+=1
        elif L==[0,1,2]:
            n012+=1    
        elif L==[0,3,0]:
            n030+=1
        elif L==[0,3,2]:
            n032+=1
        elif L==[0,2,0]:
            n020+=1
        elif L==[0,2,1]:
            n021+=1
        elif L==[0,2,3]:
            n023+=1    
        else:
            print("Error: ",L," is not a walk of length 2 starting from 0")
    print("Random walks of length 2:")
    print("Frequency of 010 (should be close to 0.166): ",int(n010*1000/N)/1000)
    print("Frequency of 012 (should be close to 0.166): ",int(n012*1000/N)/1000)
    print("Frequency of 030 (should be close to 0.166): ",int(n030*1000/N)/1000)
    print("Frequency of 032 (should be close to 0.166): ",int(n032*1000/N)/1000)
    print("Frequency of 020 (should be close to 0.11): ",int(n020*1000/N)/1000)
    print("Frequency of 021 (should be close to 0.11): ",int(n021*1000/N)/1000)  
    print("Frequency of 023 (should be close to 0.11): ",int(n023*1000/N)/1000)



def test_cover_walk():
    stop=False
    for i in range(1000):
        L=g.random_walk_till_covered()
        if not test_validity_walk(L):
            print("Walk ",L," not valid")
            stop=True
    if stop:    
        return    
    hist_lengths=[0 for i in range(0,12)]
    N=100000
    for i in range(N):
        L=g.random_walk_till_covered()
        hist_lengths[min(len(L),11)]+=1
    print("Histogram of lengths: ",[int(100*x/N)/100 for x in hist_lengths])  
    print("Should be close to:    [0.0, 0.0, 0.0, 0.0, 0.11, 0.2, 0.15, 0.13, 0.09, 0.07, 0.05, 0.17]"),
        

def test_validity_walk(L):
    n0=0; n1=0; n2=0; n3=0
    nr_copies=[0 for i in range(4)]
    res=True
    for x in L:
        nr_copies[x]+=1
    if L[0]!=0:
        print("Error: walk should start with 0")
        res=False
    for i in range(4):
        if nr_copies[i]==0:
            print("Error: the walk has not visited ",i)
            res=False
    if nr_copies[L[-1]]!=1:
        print("Error: the walk ends at ",L[-1]," and it visits it ",nr_copies[L[-1]]," times, but it should visit it just once")
        res=False   
    return res  

def test_random_tree():
    trees=[{1:0,2:1,3:0},{1:0,2:1,3:2},{1:2,2:3,3:0},{1:0,2:3,3:0},{1:0,2:0,3:2},{1:0,2:0,3:0},{1:2,2:0,3:2},{1:2,2:0,3:0}]
    counts=[0 for i in range(8)]
    N=10000
    for i in range(N):
        t=g.random_tree()
        idx=find_in_tab(t,trees)
        if idx>=0:
            counts[idx]+=1
        else:
            print("Error: your method has returned ",t," which is not a spanning tree")
    print("Frequencies of the 8 trees (each should be close to 0.12)")        
    for i in range(8):
        print("Frequency of ",trees[i],": ",int(counts[i]*100/N)/100)
        
def find_in_tab(x,L):
    for i in range(len(L)):
        if x==L[i]:
            return i
    return -1
    
test_random_neighbour()
test_random_walk()
test_cover_walk()    
test_random_tree()  

