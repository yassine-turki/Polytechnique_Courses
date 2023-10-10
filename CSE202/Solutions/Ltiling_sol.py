import random
import matplotlib.pyplot as plt

Llist=[] # the list of triples giving the tiling by L-shapes

## QUESTION 1

def middleL(n,i,j,a,b): # returns the triple giving the middle L for the (n,i,j,a,b) punctured grid
    i2=i+2**(n-1)
    j2=j+2**(n-1)
    res=[]
    if a<i2:
        res=[(i2,j2),(i2,j2-1)]
        if b<j2:
            res.append((i2-1,j2))
        else:
            res.append((i2-1,j2-1))
    else:
        res=[(i2-1,j2-1),(i2-1,j2)]
        if b<j2:
            res.append((i2,j2))
        else:
            res.append((i2,j2-1))
    return res

## QUESTION 2

def lower_left_hole(n,i,j,a,b): # returns the coordinates of the hole of the lower left quadrant
    i2=i+2**(n-1)
    j2=j+2**(n-1)
    if a<i2 and b<j2:
        return a,b
    else:
        return i2-1,j2-1

def lower_right_hole(n,i,j,a,b): # returns the coordinates of the hole of the lower right quadrant
    i2=i+2**(n-1)
    j2=j+2**(n-1)
    if a>=i2 and b<j2:
        return a,b
    else:
        return i2,j2-1

def upper_left_hole(n,i,j,a,b): # returns the coordinates of the hole of the upper left quadrant
    i2=i+2**(n-1)
    j2=j+2**(n-1)
    if a<i2 and b>=j2:
        return a,b
    else:
        return i2-1,j2
    
def upper_right_hole(n,i,j,a,b): # returns the coordinates of the hole of the upper right quadrant
    i2=i+2**(n-1)
    j2=j+2**(n-1)
    if a>=i2 and b>=j2:
        return a,b
    else:
        return i2,j2

## QUESTION 3

def tile(n,i,j,a,b):
    global Llist
    if n==0: 
        return
    Llist.append(middleL(n,i,j,a,b))
    i2=i+2**(n-1)
    j2=j+2**(n-1)
    k,l=lower_left_hole(n,i,j,a,b)
    tile(n-1,i,j,k,l)
    k,l=lower_right_hole(n,i,j,a,b)
    tile(n-1,i2,j,k,l)
    k,l=upper_left_hole(n,i,j,a,b)
    tile(n-1,i,j2,k,l)
    k,l=upper_right_hole(n,i,j,a,b)
    tile(n-1,i2,j2,k,l)

## FUNCTION (GIVEN) TO DISPLAY A TILING OF SIZE n (WITH THE HOLE POSITION CHOSEN AT RANDOM)

def display_tiling_with_random_hole(n):
    global Llist
    Llist=[]
    N=2**n
    tile(n,0,0,random.randrange(N),random.randrange(N))
    #print(Llist)	
    data=[[[0,0,0] for _ in range(N)] for _ in range(N)]
    for L in Llist:
        r=random.randrange(256)
        g=random.randrange(256)
        b=random.randrange(256)
        for entry in L:
            data[entry[0]][entry[1]]=[r,g,b]
    #print(data)
    plt.imshow(data,origin='lower')
    plt.show()

## CALL TO THE DISPLAY FUNCTION (UNCOMMENT ONCE TESTS ARE OK)

# display_tiling_with_random_hole(2)	
