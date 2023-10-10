import sys
sys.setrecursionlimit(120)

import random

def random_increasing_integer_sequence(length):
    """Return an increasing list of integers of the given length."""
    current = 0
    res = []
    for i in range(length):
        current += random.randint(1, 10)
        res.append(current)
    return res

def pp_words():
    with open('sortedpp.txt') as file:
        return [w.strip() for w in file]
    
def is_palindrome(word):
    """Check if input is a palindrome."""
    if len(word)==1 or len(word)==0: 
        return True
    if word[0] != word[len(word)-1]: 
        return False
    return is_palindrome(word[1:-1])
    

def rec_pow(a, b):
    """Compute a**b recursively"""
    if b == 0:
        return 1
    if b == 1:
        return a
    if b % 2 == 0:
        return rec_pow(a, b/2)**2
    if b % 2 == 1:
        return (rec_pow(a,(b-1)/2)**2) * a
        
        
def binary_search(sorted_list, lower, upper, element):
    """Return the position of the element in the sublist of sorted_list
    starting at position lower up to (but excluding) position upper 
    if it appears there. Otherwise return -1.
    """ 
    m=(upper+lower)//2
    if element> sorted_list[len(sorted_list)-1]:
        return -1
    if len(sorted_list[lower:upper])==1 :
        if sorted_list[m] == element:
            return m
        else:
            return -1
        return 0 
    if sorted_list[m] == element :
                return m
    elif sorted_list[m] > element :
        return binary_search(sorted_list, lower, m, element)
    elif sorted_list[m] < element :
                return binary_search(sorted_list, m, upper, element)
    else:
        return -1
    
def binary_search_simple(sorted_list, element):
    """Return the position of the element in sorted_list if it appears 
    there. Otherwise return -1.
    """
    m = len(sorted_list) // 2
    if len(sorted_list) == 1:
        if sorted_list[m]==element:
            return m
        else:
            return -1
    elif sorted_list[m] == element:
        return m
    else:
        if sorted_list[m] < element:
            r = binary_search_simple(sorted_list[m:], element)
            if r!=-1:
                return m + r 
            else:
                return -1
        else:
            return binary_search_simple((sorted_list[:m]), element)
  
def read_positive_integer(text, position):
    """Read a number starting from the given position, return it and the first
    position after it in a tuple. If there is no number at the given position
    then return None.
    """
    n=None
    numbers=['0','1','2','3','4','5','6','7','8','9']
    if text[position].isdigit() is not True:
            return None
    if len(text)==1:
            if binary_search_simple(numbers, text[position])!=-1:
                return((text, len(text)))
    
    else:
        empty=''
        for i in range(position,len(text)):
            if text[i].isdigit() :
                 empty+=(text[i])
                 n=(int(empty),i+1)
            else:
                return n
        return n



def evaluate(expression, position):
    """Evaluate the expression starting from the given position.
    Return the value and the first position after the read
    sub-expression. If the string starting at the given expressio
    is not an arithmetic expression, return None.
    """
    term=0
    if expression[position].isdigit() is True:
        return read_positive_integer(expression, position) 
    if expression[position]=='(':
        a,b=evaluate(expression, position+1)
        o=expression[b]
        c,b=evaluate(expression, b+1)
        if o =='+':
           term=a+c
        if o == '*':
            term=a*c  
        if  o == '-':
            term=a-c
        return(term,b+1)