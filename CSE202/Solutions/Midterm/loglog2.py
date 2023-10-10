# -*- coding: utf-8 -*-

import math
import hashlib

def bin_hash(x):
  hash_object = hashlib.sha1(str(x).encode('utf-8'))
  hexa=hash_object.hexdigest()
  bina=bin(int(hexa, 16))[2:].zfill(160)[:32]
  return bina
  
def cardinality(tab):
  pass
  
def bucket(bina,b):
  pass
  
def zeros(bina,b):
  pass
  
def sketch(L,b):
  pass
      
def constant(b):
  if b==4: return 0.673
  elif b==5: return 0.697
  elif b==6: return 0.709
  else: return 0.7213/(1+1.079/2**b)    
  
def loglog(L,b):
  pass
  
def loglog_small_range_correction(L,b):
  pass    
