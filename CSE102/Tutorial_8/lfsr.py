def tap_uint16(x, i):
    """ Return 1 or 0 depending on whether the ith-least significant bit
        of x is 1 or 0.
    """
    return  1 & (x >> i) 

def polytap_uint16(x, I):
    """ Tap x at all the positions in I (which is a list of tap
        positions) and return the xor of all of these tapped values.
    """
    b = 0
    for i in I:
        b ^= tap_uint16(x, i)
    return b

def lfsr_uint16(x, I):
    """Return the successor of x in an LFSR based on tap positions I"""
    return (x >> 1) | (polytap_uint16(x, I) << 15)