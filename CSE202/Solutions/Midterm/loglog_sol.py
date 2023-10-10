import math
import hashlib

def bin_hash(x):
	hash_object = hashlib.sha1(str(x).encode('utf-8'))
	hexa=hash_object.hexdigest()
	bina=bin(int(hexa, 16))[2:].zfill(160)[:32]
	return bina
	
### CODE TO BE COMPLETED	
	
def cardinality(tab):
	present={}
	for x in tab:
		if not x in present:
			present[x]=True
	return len(present)

def bucket(bina,b): # returns the integer corresponding to the leftmost b bits in bina
	return (int)(bina[:b],2)
	
def zeros(bina,b): # return the largest l, called b-length of bina, such that all entries in bina[b:b+l] are zeros
	for i in range(len(bina)-b):
		if bina[b+i]=='1':
			return i
	return len(bina)-b
		
def sketch(L,b): # returns the array A of length 2**b, such that A[i] is 0 if the bucket of index i is empty, and otherwise A[i] is one plus the maximum value taken by the b-length over all elements in the bucket of index i  
	A=[0 for _ in range(2**b)]
	for x in L:
		bina=bin_hash(x)
		i=bucket(bina,b)
		A[i]=max(A[i],1+zeros(bina,b))
	return A
		
def constant(b): # function to compute the constant alpha(b), given
	if b==4: return 0.673
	elif b==5: return 0.697
	elif b==6: return 0.709
	else: return 0.7213/(1+1.079/2**b)
								

def loglog(L,b):
	sket=sketch(L,b)
	Somme=0
	m=2**b
	for i in range(m):
		Somme += 2**(-sket[i])
	return constant(b)*m**2/Somme	
	
def loglog_small_range_correction(L,b):
	m=2**b
	E=loglog(L,b)
	if E<=5*m/2:
		sket=sketch(L,b); #print("correction")
		V=0
		for i in range(m):
			if sket[i]==0: V+=1	
		if V==0:
			return E
		else:
			#print("small range corrections")
			return m*math.log(m/V)	
	else:
		return E				
