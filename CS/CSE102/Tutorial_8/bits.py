def uint16_to_bitstring(x):
    l=[]
    for i in range(16):
        l.append( 0b1&(x >> (15 - i)))
    return l
def bitstring_to_uint16(bs):
    a=0
    for i in range(len(bs)):
        a+=(bs[i] << (15-i))
    return a
def mod_pow2(x, k):
    return ((1 << k) - 1) & x

def is_pow2(x):
    return (x & (x - 1) == 0) and not(0 >= x) 

def set_mask(w, m):
    """set every bit position which is 1 in m, to 1 in w"""
    return w | m

def toggle_mask(w, m):
    """toggle every bit position which is 1 in m, in w"""
    return w ^ m

def clear_mask(w, m):
    """set every bit position which is 1 in m, to 0 in w"""
    return  (~ m) & w 


    