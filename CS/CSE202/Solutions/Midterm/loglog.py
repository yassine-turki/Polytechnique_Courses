import math
import hashlib

def bin_hash(x):
	hash_object = hashlib.sha1(str(x).encode('utf-8'))
	hexa=hash_object.hexdigest()
	bina=bin(int(hexa, 16))[2:].zfill(160)[:32]
	return bina
	
### CODE TO BE COMPLETED	
	
def cardinality(tab):
	pass
	
def bucket(bina,b): # returns the integer corresponding to the leftmost b bits in bina
	pass
	
def zeros(bina,b): # return the largest l, called b-length of bina, such that all entries in bina[b:b+l] are zeros
	pass
		
def sketch(L,b): # returns the array A of length 2**b, such that A[i] is 0 if the bucket of index i is empty, and otherwise A[i] is one plus the maximum value taken by the b-length over all elements in the bucket of index i  
	pass
		
def constant(b): # function to compute the constant alpha(b), given
	if b==4: return 0.673
	elif b==5: return 0.697
	elif b==6: return 0.709
	else: return 0.7213/(1+1.079/2**b)
								

def loglog(L,b):
	pass
	
def loglog_small_range_correction(L,b):
	pass				
