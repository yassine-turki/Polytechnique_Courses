# Question 1
def middleL(n, i, j, a, b): # returns the middle of the punctured grid of type (n, i, j, a, b)
    l=[]
    halfi=i+2**(n-1)
    halfj=j+2**(n-1)
    if a<halfi:
        l.append((halfi,halfj))
        l.append((halfi,halfj-1))
        if b>=halfj:
            l.append((halfi-1,halfj-1))
        else:
            l.append((halfi-1,halfj))
    else:
        l.append((halfi-1,halfj-1))
        l.append((halfi-1,halfj))
        if b>=halfj:
            l.append((halfi,halfj-1))
        else:
            l.append((halfi,halfj)) 
    return l

# Question 2
def lower_left_hole(n, i, j, a, b): # returns the coordinates of the hole of the lower left quadrant
    halfi = i+2**(n-1)
    halfj = j+2**(n-1)
    if a < halfi and b < halfj:
        return (a,b)
    else:
        return (halfi-1,halfj-1)

def lower_right_hole(n, i, j, a, b): # returns the coordinates of the hole of the lower right quadrant
    halfi = i+2**(n-1)
    halfj = j+2**(n-1)
    if a >= halfi and b < halfj:
        return (a,b)
    else:
        return (halfi,halfj-1)

def upper_left_hole(n, i, j, a, b): # returns the coordinates of the hole of the upper left quadrant
    halfi = i+2**(n-1)
    halfj = j+2**(n-1)
    if a < halfi and b >= halfj:
        return (a,b)
    else:
        return (halfi-1,halfj)

def upper_right_hole(n, i, j, a, b): # returns the coordinates of the hole of the upper right quadrant
    halfi = i+2**(n-1)
    halfj = j+2**(n-1)
    if a >=halfi and b >= halfj:
        return (a,b)
    else:
        return (halfi,halfj)
nl=[]
# Question 3
def tile(n, i, j, a, b): # returns a list with a valid L-tiling of the punctured grid of type (n, i, j, a, b)
    halfi = i+2**(n-1)
    halfj = j+2**(n-1)
    if n==0: 
        return None
    nl.append(middleL(n,i,j,a,b))
    newa,newb=lower_left_hole(n,i,j,a,b)
    tile(n-1,i,j,newa,newb)
    newa,newb=lower_right_hole(n,i,j,a,b)
    tile(n-1,halfi,j,newa,newb)
    newa,newb=upper_left_hole(n,i,j,a,b)
    tile(n-1,i,halfj,newa,newb)
    newa,newb=upper_right_hole(n,i,j,a,b)
    tile(n-1,halfi,halfj,newa,newb)
    return nl
    
    
