# -*- coding: utf-8 -*-

import math
from PowerTree import *

## Q1 ##
def bin_pow(x,n):
    if n==0:
        return 1
    if n==1:
        return x
    if n%2==1:
        return x*((bin_pow(x,n//2)))**2
    return bin_pow(x, n//2)**2

## Q2 ##
def cost_bin_pow(n):
    if n==0 or n==1:
        return 0
    if n%2==1:
        return 2 + cost_bin_pow(n//2)
    return 1+ cost_bin_pow(n//2)

## Q3 ##
def smallest_factor(n):
    for i in range(2,math.floor(math.sqrt(n))+1):
        if n%i==0:
            return i
    return -1

## Q4 ##
def factor_pow(x,n):
    if n==0:
        return 1
    if n==1:
        return x
    if smallest_factor(n)!=-1:
        p=smallest_factor(n)
        q=n/p
        return factor_pow(x, p)**q
    return x*factor_pow(x, n-1)

## Q5 ##
def cost_factor_pow(n):
    if n==0 or n==1:
        return 0
    if smallest_factor(n)!=-1:
        p=smallest_factor(n)
        return cost_factor_pow(p)+cost_factor_pow(n/p)
    return 1 + cost_factor_pow(n-1)

## Q6 ##
def power_from_chain(x,chain):
    d=dict()
    d[1]=x
    for k in range(1,len(chain)):
        a=chain[k]
        b=chain[k-1]
        c=a-b
        d[a]=d[b]*d[c]
    return d[chain[-1]]

## Q8 ##

def power_tree_chain(n):
    t=PowerTree()
    while n not in t.parent:
        t.add_layer()
    return t.path_from_root(n)

def power_tree_pow(x,n):
    if n==0: 
        return 1
    if n==1:
        return x
    ptc= power_tree_chain(n)
    return  power_from_chain(x,ptc)
    	   
def cost_power_tree_pow(n):
   if n==0: 
       return 0
   ptc= len(power_tree_chain(n))
   return ptc-1
  
## Q9 ##  
def compare_costs(m):
    for i in range(m+1):
        print(f'{i}: cost_bin_pow: {cost_bin_pow(i)} / cost_factor_pow: {cost_factor_pow(i)} / cost_power_tree_pow: {cost_power_tree_pow(i)}')

def test9():
    if cost_power_tree_pow(23) == 6:
        print("Test9 ok")
        return True
    else:
        print("cost_power_tree_pow founded : " + str(cost_power_tree_pow(23)))
        return False
    
test9()


