#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Sep 23 08:11:02 2021

@author: yassine.turki
"""

def hello_world():
    """
    returns 'Hello world!'
    
    """
    return 'Hello world!'

def check_day(n):
    """
    Given an integer between 1 and 7 inclusive,
    return either string 'work!' or string 'rest!'
    depending on whether the day is a workday or not
    """
    if n < 1 or n > 7:
        return None # invalid m
    elif 5>= n >= 1:
        return 'work!'
    else:
        return 'rest!'
def name_of_month(m):
    """Given an integer m between 1 and 12 inclusive,
    indicating a month of the year, returns the name of that month.
    For example: name_of_month(1) == 'January' and name_of_month(12) == 'December'.
    If the month does not exist (that is, if m is outside the legal range),
    then this function returns None.
    """
    if m < 1 or m > 12:  # Non-existent month
        return None
    elif m == 1:
        return 'January'
    elif m == 2:
        return 'February'
    elif m == 3:
        return 'March'
    elif m == 4:
        return 'April'
    elif m == 5:
        return 'May'
    elif m == 6:
        return 'June'
    elif m == 7:
        return 'July'
    elif m == 8:
        return 'August'
    elif m == 9:
        return 'September'
    elif m == 10:
        return 'October'
    elif m == 11:
        return 'November'
    else: 
        return 'December'

def str_with_suffix(n):
    """Convert the integer n to a string expressing the corresponding 
    position in an ordered sequence.
    Eg. 1 becomes '1st', 2 becomes '2nd', etc.
    """
    if 13 >= n >= 11:
        return str(n)+'th'
    elif n % 100 == 11:
        return str(n)+'th'
    elif n % 100 == 12:
        return str(n)+'th'
    elif n % 100 == 13:
        return str(n)+'th'
    elif n % 10 == 1:
        return str(n)+'st'
    elif n % 10 == 2:
        return str(n)+'nd'
    elif n % 10 == 3:
        return str(n)+'rd'
    else:
        return str(n)+'th'
    
def is_leap_year(y):
    """ Return True if y is a leap year, False otherwise. """
    if y % 4 == 0 :
        if y % 100 == 0 :
            if y % 400 == 0 :
                return True
            else:
                return False
        else:
            return True
    elif y == 0 :
            return True
    else:
        return False
    
    
def number_of_days(m, y):
    """Returns the number of days in month m of year y."""
    
    if m == 2:
        if is_leap_year(y) == True:
            return 29
        else:
            return 28
    if m == 1 or m == 3 or m == 5 or m == 7 or m == 8 or m == 10 or m == 12 :
        return 31
    else :
        return 30
    
def date_string(d, m, y):
    
    if m < 1 or m > 12 :  # Non-existent month
        return 'Nonexistent date'
    if is_leap_year(y) == False and m == 2 :
        if d <= 28 :
            return 'The '+ str(str_with_suffix(d)) + ' of ' + str(name_of_month(m)) + ', ' + str(y)
        if d >= 29 :    
            return 'Nonexistent date'
    if d >= 32:
        return 'Nonexistent date'
    if m == 0 or d == 0:
        return 'Nonexistent date'
    if m == 1 or m == 3 or m == 5 or m == 7 or m == 8 or m == 10 or m == 12 :
        if d <= 31:
            return 'The '+ str(str_with_suffix(d)) + ' of ' + str(name_of_month(m)) + ', ' + str(y)
        elif d > 31:
            return 'Nonexistent date'
    if m == 2 or m == 4 or m == 6 or m == 9 or m == 11:
        if d <= 30:
            return 'The '+ str(str_with_suffix(d)) + ' of ' + str(name_of_month(m)) + ', ' + str(y)
        elif d > 30:
            return 'Nonexistent date'   
    else: 
        return 'The '+ str(str_with_suffix(d)) + ' of ' + str(name_of_month(m)) + ', ' + str(y)
    
def time_string(n):
    """Takes a number of seconds n as an argument,
    and returns a string describing the corresponding number of days, hours, minutes, and seconds.
    """  
    d = n // 86400 
    h = (n % 86400) // 3600
    m = ((n % 86400) % 3600) // 60
    s= ((n % 86400) % 3600) % 60
    l=''
    if d == 1:
        l= l + str(d)+' day, '
    elif d > 1:
        l= l + str(d) + ' days, '
    if h == 1:
        l = l + str(h) + ' hour, '
    if h > 1:
        l = l + str(h) + ' hours, '
    if m == 1:
        l = l + str(m) + ' minute, '
    if m > 1:
        l = l + str(m) + ' minutes, '
    l = l + str(s) + ' second'
    if s > 1 or s == 0:
        l = l +'s'
    return l

    
    

              
    
   
      
    
    
        
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    