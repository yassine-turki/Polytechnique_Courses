#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Oct  7 08:14:16 2021

@author: yassine.turki
"""
import math

    
def average(numlist):
    """Return average of list of numbers"""
    return round(sum(numlist)/len(numlist), 2)

def string_floats_to_list(string_floats):
    """Return a list from the string of floats string_floats."""
    a=[float(x)for x in string_floats.split() ]
    return a

def student_data(data_string):
    """Compute (name, results) tuple from the string data_string."""
    s=data_string.split()
    n= s[0]
    r=s[1:]
    results=[float(x) for x in r]
    return (n, results)

def tuple_to_string(name, results):
    """Return string from (name, results) tuple"""
    s=[str(x)for x in results]
    a=' '.join(s)
    l=[name,a]
    return ' '.join(l)

def read_student_data(filename):
    """Return list of student data from file"""
    l = []
    with open(filename,'r') as file:
        a = file.readlines()
        i=0
        while i<len(a):
            b=student_data(a[i])
            l.append(b)
            i+=1
    return l



def extract_averages(filename):
    """Return list of name and average for each line in file"""
    a=read_student_data(filename)
    l=[]
    for i in range(len(a)):
        b=average(a[i][1])
        c=a[i][0]
        t=(c,b)
        l.append(t)
        i+=1
    return l


def discard_scores(numlist):
    """Filter numlist: construct a new list from numlist with
    the first two, and then the lowest two, scores discarded.
    """
    a=[]
    for i in range(len(numlist)):
        a.append(numlist[i])
    a.remove(a[0])
    a.remove(a[0])
    a.remove(min(a))
    a.remove(min(a))
    return a

 
def summary_per_student(infilename, outfilename):
    """Create summaries per student from the input file 
    and write the summaries to the output file.
    """
    data = read_student_data(infilename)
    v = 0
    with open(outfilename,'w') as outfile:
        for i in range(len(data)):
            c=discard_scores(data[i][1])
            s=round(sum(c),2)
            v += s
            outfile.write(data[i][0])
            outfile.write(' ')
            for elements in c:
                outfile.write(str(elements))
                outfile.write(' ')
            outfile.write('sum: ')
            outfile.write(str(s))
            outfile.write('\n')
        outfile.write('total average: ')
        outfile.write(str(round(v/len(data),2)))
        outfile.write('\n')
        
    
def summary_per_tutorial(infilename, outfilename):
    """Create summaries per student from infile and write to outfile."""
    data = read_student_data(infilename)
    a=data[0][1]
    with open(outfilename,'w') as outfile:
       for n in range(len(a)):
          l=[]
          for i in range(len(data)):
              c=data[i][1][n]
              l.append(c) 
          outfile.write('TD')
          outfile.write(str(n+1))
          outfile.write(': ')
          outfile.write('average: ')
          outfile.write(str(average(l)))
          outfile.write(' min: ')
          outfile.write(str(min(l)))
          outfile.write(' max: ')
          outfile.write(str(max(l)))
          outfile.write('\n')
    print(l)

