import random
def is_prime (n,k=32):
    if n%2==0 and n!=2:
        return False
    d=n-1
    r=0
    while d%2==0:
       d//=2
       r+=1
    for _ in range(k): 
        a=random.randint(2,n-2)
        #print(a,d,n)
        x=pow(a,d,n)
        if x==1 or x==n-1:
            continue
        t=0
        for i in range(r-1):
            x=(x**2)%n
            if x==1:
                return False
            if x==n-1 :
                break
            t+=1
        if t==r-1:
            return False
    return True