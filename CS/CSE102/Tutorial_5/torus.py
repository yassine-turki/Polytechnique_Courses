import random
import math

def torus_volume_cuboid(R, r, N=100_000):
    a=0
    for i in range(N):
        x = random.uniform(-R-r, R+r)
        y = random.uniform(-R-r, R+r)
        z = random.uniform(-r, r)
        b= ((math.sqrt(x ** 2 + y ** 2) - R) ** 2) + z ** 2 
        if b < r ** 2:
            a+=1
    return a/N * (8 * ((R+r) ** 2) * r)


    
    