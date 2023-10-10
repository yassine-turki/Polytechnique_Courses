def fibs():
    r0, r1 = 0, 1
    while True:
        yield r0
        r0, r1 = r1, r0+r1
def prefix_sums(k):
    a=0
    r=0
    while True:
        r+=k+a
        yield r
        a+=1