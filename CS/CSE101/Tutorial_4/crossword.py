#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Oct 14 08:15:44 2021

@author: yassine.turki
"""

def split_type(line):
    """Splits off the first word in the line and returns both parts in a tuple.
    Also eliminates all leading and trailing spaces.
    Example:
        split_type('ROW ##.##') returns ('ROW', '##.##')
        split_type('CLUE (0,1) down: Of or pertaining to the voice (5)') returns
            ('CLUE', '(0,1) down: Of or pertaining to the voice (5)')
        split_type('  ROW    ##.##   ') returns ('ROW', '##.##')

    """
    l=line.split()
    i=len(l)   
    return (l[0],' '.join(l[1:i]))


def read_row(row):
    """Reads a row of a crossword puzzle and decomposes it into a list. Every
    '#' is blocking the current box. Letters 'A', ..., 'Z' and 'a', ..., 'z'
    are values that are already filled into the box. These letters are capitalized
    and then put into the list. All other characters stand
    for empty boxes which are represented by a space ' ' in the list.
    Examples:
        read_row('#.#') gives ['#', ' ', '#']
        read_row('C.T') gives ['C', ' ', 'T']
        read_row('cat') gives ['C', 'A', 'T']
    """
    l=[]
    for i in range(len(row)):
        if row[i]=='#':
            l.append("#")
        elif row[i].isalpha():
            l.append(row[i].upper())
        elif not row[i].isalpha():
            l.append(' ')
    return l
            

def coord_to_int(coordstring):
    """Reads a coordinate into a couple in the following way: The input is of the form
        '(x,y)' where x, y are integers. The output should then be
        (x, y), where (x, y) is a tuple of values of type int.
    None of these values are strings.
    Example:
        coord_to_int('(0,1)') returns
        (0, 1)
    """
    l=coordstring.strip('()')
    cut=l.index(',') 
    x=int(l[:cut])
    y=int(l[cut+1:])
    return (x,y)


def read_clue(cluestring):
    """Reads a clue into a tuple in the following way: The input is of the form
        '(x,y) direction: question (length)'
    where x, y and length are integers, direction is 'across' or 'down'
    and question is the text of the clue. The output should then be
        ((x, y), direction, length, question)
    where (x, y) is a tuple of values of type int and length is of type int.
    There may be arbitrarily many spaces between the different parts of the input.
    Example:
        read_clue('(0,1) down: Of or pertaining to the voice (5)') returns
        ((0, 1), 'down', 5, 'Of or pertaining to the voice')
    """
    t=split_type(cluestring)
    c=coord_to_int(t[0])
    l=cluestring.split()
    num=l[len(l)-1].strip('()')
    clue=' '.join(l[2:len(l)-1])
    cut=l[1].index(':')
    return (c, l[1][:cut], int(num),clue )



def read_file(filename):
    """Opens the file with the given filename and creates the puzzle in it.
    Returns a pair consisting of the puzzle grid and the list of clues. Assumes
    that the first line gives the size. Afterwards, the rows and clues are given.
    The description of the rows and clues may interleave arbitrarily.
    """
    with open(filename, 'r') as infile:
        s=infile.readlines()
        l=[ t.strip('\n') for t in s ]
        l=[ t.strip(' ') for t in l ]
        print(l)
        rows=[]
        clues=[]
        for i in range(len(l)):
            a=l[i].find('ROW')
            if a==0:
                rows.append(l[i][a:])
        for i in range(len(rows)):
            rows[i] = read_row(split_type(rows[i])[1])
        for i in range(len(l)):
            a=l[i].find('CLUE')
            if a==0:
                clues.append(l[i][a:])
        clues=[ t.strip('CLUE') for t in clues ]
        for i in range(len(clues)):
            clues[i]=read_clue(clues[i])
        print (rows)
        return (rows,clues)
        


def create_clue_string(clue):
    """ Given a clue, which is a tuple
    (position, direction, length, question),
    create a string in the form 'position direction: question (length)'.
    For example, given the clue
        ((2, 3), 'across', 4, 'Black bird'),
    this function will return
        '(2,3) across: Black bird (4)'
    """
    a=str(clue[0]).replace(' ','')
    return f'{a} {clue[1]}: {clue[len(clue)-1]} ({clue[len(clue)-2]})'


def create_grid_string(grid):
    """Return a crossword grid as a string."""
    size = len(grid)
    separator = '  +' + ('-----+')*size
    column_number_line = '   '
    column_number_line += ''.join(f' {j:2}   ' for j in range(size))
    result = f'{column_number_line}\n{separator}\n'
    for (i, row) in enumerate(grid):
        fill = '  |'
        centre_line = f'{i:2}|'
        for entry in row:
            if entry == '#':
                fill += '#####|'
                centre_line += '#####|'
            else:
                fill += '     |'
                centre_line += f'  {entry}  |'
        result += f'{fill}\n{centre_line}\n{fill}\n{separator}\n'
    return result


def create_puzzle_string(grid, clues):
    """Return a human readable string representation of the puzzle."""   
    a = create_grid_string(grid)
    for c in clues :
        a += "\n" + create_clue_string(c) 
    return a 


def fill_in_word(grid, word, position, direction):
    """Create and return a new grid (a list of lists) based on the grid
    given in the arguments, but with the given word inserted according
    to position and direction.
        - direction: is either 'down' or 'across'.
        - position: the coordinates of the first letter of the word in the grid.
    *This function may modify its grid argument!*
    """
    l=[]
    L=[]
    x,y=position[0],position[1]
    if direction.find('across')==0:
        for i in word:
            l.append(i)
        for i in range(len(l)):
            grid[x][y]=l[i]
            y+=1
    elif direction.find('down')==0:
        for i in word:
            L.append(i)
        for i in range(len(L)):
            grid[x][y]=L[i]
            x+=1
    return grid

def create_row_string(row):
    """Returns a row representation of a string.
    Example:
        create_row_string(['#', 'A', ' ']) returns '#A.'
    """
    a=read_row(row)
    b=''.join(a)
    c=b.replace(' ','.')
    return c
    
def write_puzzle(filename, grid, clues):
    """Writes the puzzle given by the grid and by the clues to the specified
    file.
    """
    with open(filename,'w') as out:
        size=len(grid)
        out.write(f'SIZE {size}\n')
        for r in grid:
            out.write(f'ROW {create_row_string(r)}\n')
        for c in clues:
            out.write(f'CLUE {create_clue_string(c)}\n')
            
    
        
        
        
    
    
    
    
    
    
    
    