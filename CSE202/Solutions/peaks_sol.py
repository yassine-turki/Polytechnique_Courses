# -*- coding: utf-8 -*-

# Question 1

def peak_naive(L):
  for i in range(len(L)-1):
    if(L[i]>=L[i+1]):
      return i
  return len(L)-1
  
# Question 2  

def peak_aux(L,p,q):
  if(q==p+1):
    return p
  else:
    l=(p+q)//2
    if(L[l-1]>=L[l]):
       if l-1==p or L[l-1]>=L[l-2]: 
            return l-1
       else:
          return peak_aux(L,p,l)
    else:
       if l==q-1 or L[l]>=L[l+1]:
            return l
       else:
          return peak_aux(L,l,q)

def peak(L):
  return peak_aux(L,0,len(L))
  
# Question 3  
	
def is_peak(M,i,j):
   I=len(M)
   J=len(M[0])
   if i>0 and M[i][j]<M[i-1][j]:
     return False
   if i<I-1 and M[i][j]<M[i+1][j]:
     return False
   if j>0 and M[i][j]<M[i][j-1]:
     return False
   if j<J-1 and M[i][j]<M[i][j+1]:
     return False
   return True

# Question 4

def peak2d_naive(M):
  I=len(M)
  J=len(M[0])
  for i in range(I):
   for j in range(J):
     if is_peak(M,i,j):
        return (i,j)

# Question 5    

def Aset(p,q):
  if q<=p+4:
    return range(p,q)
  else:
    l=(p+q)//2
    return [p,l-1,l,q-1]
    
def pivot(M,p,q,r,s):
  Apq=Aset(p,q)
  Ars=Aset(r,s)
  max_pos=(p,r)
  max_val=M[p][r]
  for i in Apq:
    for j in range(r,s):
       if M[i][j]>max_val:
         max_val=M[i][j]
         max_pos=(i,j)
  for i in range(p,q):
    for j in Ars:
       if M[i][j]>max_val:
         max_val=M[i][j]
         max_pos=(i,j)
  return max_pos

# Question 6

def peak2d_aux(M,p,q,r,s): # assume M[p:q][r:s] is a good submatrix
  (i,j)=pivot(M,p,q,r,s)
  if is_peak(M,i,j): # always true if q-p<=4 or s-r<=4
    return (i,j)
  l=(p+q)//2
  m=(r+s)//2
  if i<l: 
    if j<m:
      return peak2d_aux(M,p,l,r,m)
    else:
      return peak2d_aux(M,p,l,m,s)
  else: 
    if j<m:
      return peak2d_aux(M,l,q,r,m)
    else:
      return peak2d_aux(M,l,q,m,s)

def peak2d(M):
 return peak2d_aux(M,0,len(M),0,len(M[0]))
