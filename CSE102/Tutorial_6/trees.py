import math

class Node:
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right

def size(root):
    if root==None:
        return 0
    r=root.right
    l=root.left
    return 1 + size(r) + size(l)

def sum_values(root):
    if root==None:
        return 0
    r=root.right
    l=root.left
    return sum_values(r)+sum_values(l)+root.value

def height(root):
    if root==None:
        return -1
    r=root.right
    l=root.left
    return max(height(l), height(r))+1

def mirrored(lroot, rroot):
    if lroot==None and rroot==None:
        return True
    if lroot==None and rroot !=None or (lroot!=None and rroot==None):
        return False
    return lroot.value==rroot.value and mirrored(lroot.left,rroot.right) and mirrored(lroot.right, rroot.left )

def check_symmetry(root):
    if root==None:
        return True
    return mirrored(root.right, root.left)

def check_BST(root):
      if root == None or (root.left == None and root.right == None):
         return True

      elif root.right == None:
         return root.left.value < root.value and check_BST(root.left)

      elif root.left == None:
         return root.right.value >= root.value and check_BST(root.right)

      return check_BST(root.left) and check_BST(root.right)
 
def min_BST(root,a=math.inf):
    if root==None:
        return a
    return min_BST(root.left,root.value)
    