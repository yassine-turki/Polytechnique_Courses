#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Sep 30 08:12:20 2021

@author: yassine.turki
"""

import random

COLORS = ['RED', 'GREEN', 'BLUE', 'PURPLE', 'BROWN', 'YELLOW']

def input_color(color):
    """Return True if the given input color can be found in COLORS
       Use a for-loop to iterate over the list of COLORS.
    """
    for c in COLORS :
        if c==color:
            return True
    return False
        

def create_code():
    """Return 4-element list of strings randomly chosen from
    COLORS with repetition.
    """
    r= [random.choice(COLORS), random.choice(COLORS), random.choice(COLORS), random.choice(COLORS)]
    return r

def black_pins(guess, code):
    """guess, code: 4-element lists of strings from COLORS
    Returns the number of black pins, determined by the standard
    Mastermind rules
    """
    b=0
    for n in range (len(guess)):
       if guess[n] == code[n]:
           b += 1
    return b

def score_guess(guess, code):
    """guess, code: 4-element lists of strings
    Return (black, white) where
    black is the number of black pins (exact matches), and
    white is the number of white pins (correct colors in wrong places)
    """
    black = black_pins(guess, code)
    g=0
    for i in range (len(COLORS)):
        g += min(guess.count(COLORS[i]), code.count(COLORS[i]))
    w= g-black
    return (black,w)

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

       
def input_guess():
    """Input four colors from COLORS and return as list.
    """
    
    print('Enter your guess:')
    b=[]
    i=0
    while i<4:       
        c=input(str_with_suffix(i+1)+ ' color: ')
        b.append(c)
        i+=1
        if input_color(c) == False:
            print ("Please input a color from the list "+ str(COLORS))
            b.remove(c)    
            i=i-1
    return b

def score_guess2(guess, code):
    """guess, code: 4-element lists of strings
    Return (black, white) where
    black is the number of black pins (exact matches), and
    white is the number of white pins (correct colors in wrong places)
    """
    black = black_pins(guess, code)
    g=0
    for i in range (len(COLORS)):
        g += min(guess.count(COLORS[i]), code.count(COLORS[i]))
    w= g-black
    return "Score: "+ str(black)+" black, "+ str(w)+ " white"

def one_round(code):
    """Input guess, score guess, print result, and return True iff
    user has won.
    """
    a=input_guess()
    score_guess2(code, a)
    b = black_pins(code, a)
    print(score_guess2(code, a))
    if b== 4:
        return True
    else:
        return False
        
def play_mastermind(code):
    """Let user guess the code in rounds, use a while-loop
    """
    n=1
    print("Round 1")
    while one_round(code)== False:
            n+=1 
            print("Round " + str(n))
    print ('You win!')
    # Selim Khouaja helped me remove unecessary code in this function


    


    
        
            
            
        
        
    
    
    
    
    
       