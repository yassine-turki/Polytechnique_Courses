# -*- coding: utf-8 -*-

import math
from PowerTree import *

## Q1 ##
def bin_pow(x,n):
    if n  == 0:
        return 1 
    if n == 1: 
        return x
    tmp = bin_pow(x, n//2)
    tmp = tmp*tmp
    if n%2==0: return tmp 
    return tmp*x
    

## Q2 ##
def cost_bin_pow(n):
    if n == 0 or n == 1 :
        return 0
    
    if n%2 == 0:
        return 1 + cost_bin_pow(n//2)
    else: 
        return 2 + cost_bin_pow(n//2)
    
## Q3 ##
def smallest_factor(n):
    for i in range(2, int(math.sqrt(n))+1):
        if n%i == 0: 
            return i 
    return -1 
    
## Q4 ##
def factor_pow(x,n):
    if n == 0: return 1
    if n == 1 : return x
    
    if n >= 2 : 
        p = smallest_factor(n)
        if p == -1 :
            return x * factor_pow(x, n-1)
        else:
            q = n / p
            tmp = factor_pow(factor_pow(x, p), q)
            return tmp
        
        
## Q5 ##
def cost_factor_pow(n):
    if n == 0 or n == 1: 
        return 0
    if n>=2:
        p = smallest_factor(n)
        if p == -1:
            return 1 + cost_factor_pow(n-1)
        else:
            return  cost_factor_pow(p) + cost_factor_pow(n/p)

## Q6 ##
def power_from_chain(x,chain):
    powers = {0:1, 1:x}
    n = chain[-1]
    for a in range(1, len(chain)):
        k = chain[a]
        i = chain[a-1]
        j = k-i
        powers[k] = powers[i] * powers[j]
    
    return powers[n]

## Q8 ##

def power_tree_chain(n):
    tree = PowerTree()
    while n not in tree.parent:
        tree.add_layer()
    return tree.path_from_root(n)

def power_tree_pow(x,n):
    if n == 0: return 1
    if n == 1: return x 
    chain = power_tree_chain(n)
    res = power_from_chain(x, chain)
    return res 
    	   
def cost_power_tree_pow(n):
    if n == 0 or n == 1:
        return 0 
    else:
        chain = power_tree_chain(n)
        res = len(chain) -1
    return res
  
## Q9 ##  
def compare_costs(m):
    for n in range(m+1):
        print('bin_pow(x,',str(n)+') :', cost_bin_pow(n))
        print('factor_pow(x,',str(n)+') :', cost_factor_pow(n))
        print('power_tree_pow(x,',str(n)+') :', cost_power_tree_pow(n))
        print('\n')
        
def test9():
    if cost_power_tree_pow(23) == 6:
        print("Test9 ok")
        return True
    else:
        print("cost_power_tree_pow founded : " + str(cost_power_tree_pow(23)))
        return False
    
test9()



