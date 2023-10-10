class Node:
    def __init__(self, key, value, left, right):
        self.key = key
        self.value = value
        self.left = left
        self.right = right

    def __eq__(self, other):
        return self.key == other.key \
           and self.value == other.value \
           and self.left == other.left \
           and self.right == other.right

    def __repr__(self):
        return f'Node({repr(self.key)}, {repr(self.value)}, {repr(self.left)}, {repr(self.right)})'

    def __str__(self):
        lines, _ = self._str_aux()
        return '\n'.join(lines)

    def _str_aux(self):
        # Recursive helper for __str__.
        # Returns lines (to be joined) and the horizontal position where
        # a branch from an eventual parent should be attached.
        label = f'{self.key}: {self.value}'

        # Leaf case
        if self.right is None and self.left is None:
            return [label], len(label) // 2
    
        if self.left is None:
            llines, lpos, lwidth, ltop0, ltop1, lfill = [], 0, 0, '', '', ''
        else:  # Recurse left
            llines, lpos = self.left._str_aux()
            lwidth = len(llines[0])
            ltop0 = lpos*' ' + ' ' + (lwidth - lpos - 1)*'_'
            ltop1 = lpos*' ' + '/' + (lwidth - lpos - 1)*' '
            lfill = lwidth*' '
            
        if self.right is None:
            rlines, rpos, rwidth, rtop0, rtop1, rfill = [], 0, 0, '', '', ''
        else:  # Recurse right
            rlines, rpos = self.right._str_aux()
            rwidth = len(rlines[0])
            rtop0 = rpos*'_' + ' ' + (rwidth - rpos - 1)*' '
            rtop1 = rpos*' ' + '\\' + (rwidth - rpos - 1)*' '
            rfill = rwidth*' '

        cfill = len(label)*' '
        
        # Extend llines or rlines to same length, filling with spaces (or '')
        maxlen = max(len(llines), len(rlines))
        llines.extend(lfill for _ in range(maxlen - len(llines)))
        rlines.extend(rfill for _ in range(maxlen - len(rlines)))
          
        res = []
        res.append(ltop0 + label + rtop0)
        res.append(ltop1 + cfill + rtop1)
        res.extend(lline + cfill + rline for (lline, rline) in zip(llines, rlines))
        
        return res, lwidth + len(label) // 2
    
    def search(self, key):
        """ 
        Returns the value of the node with key key, if key is found in the tree; otherwise, it returns None.
        """
        if key == self.key:
            return self.value
        if key < self.key:
            if self.left is None:
                return None
            else:
                return self.left.search(key)
        if key > self.key:
            if self.right is None:
                return None
            else:
                return self.right.search(key)
    
    def print_in_order(self):
        """
        prints all keys and values in the tree, sorted in increasing order.
        """
        if self.left is not None:
            self.left.print_in_order()
        print(f'{self.key}: {self.value}')
        if self.right is not None:
            self.right.print_in_order()
    
    def add(self, key, value):
        """
        
        If k < node.key, then k should be inserted into the left subtree of node. Hence,
            if node.left is None, then we create a new node at node.left with key k and value [v] (that is, we start a new list of line numbers for that word).
            If node.left is not None, then we repeat the procedure recursively on node.left.
        Similarly, if k > node.key, then we either create a new node at node.right with key k and value [v], or we recurse on the right subtree of node.
        If k == node.key, then the word k is already in the tree, so we check if v is already in node.value (the list of line numbers where k appears); if it does not yet appear there, then we append it.
        """
        if key < self.key:
            if self.left is None:
                self.left= Node(key,[value],None,None)
            else:
                self.left.add(key,value)
        if key > self.key:
            if self.right is None:
                self.right= Node(key,[value],None,None)
            else:
                self.right.add(key,value)
        if key == self.key:
            if value not in self.value:
                self.value.append(value)
    
    def write_in_order(self, filename):
        """Write all key: value pairs in the index tree
        to the named file, one entry per line.
        """
        with open(filename, 'w') as file:
            self.write_in_order_rec(file)

    def write_in_order_rec(self, file):
        """Recursive helper method for write_in_order."""
        if self.left is not None:
           self.left.write_in_order_rec(file)
        file.write(f'{self.key}: {self.value}\n')
        if self.right is not None:
           self.right.write_in_order_rec(file)
    def height(self):
        """ returns the height of the tree given as node."""
        if self.left is None and self.right is None:
            return 0
        if self.right is None:
           return (self.left.height())+1
        if self.left is None:
           return (self.right.height())+1
        return max(self.right.height(),self.left.height())+1
    def list_in_order(self):
         """converts a BST to a sorted list of key-value pairs."""
         if self is None:
             return []
         if self.left is not None:
            l=self.left.list_in_order()
         else:
            l=[]
         if self.right is not None:
            p=self.right.list_in_order()
         else:
            p=[]
         return l+[(self.key,self.value)]+p
         
       
          
                
def split_in_words_and_lowercase(line):
    """Split a line of text into a list of lower-case words."""
    parts = line.strip('\n').replace('-', ' ').replace("'", " ").replace('"', ' ').split()
    parts = [p.strip('",._;?!:()[]').lower() for p in parts]
    return [p for p in parts if p != '']

def construct_bst_for_indexing(filename):
    """
    finds all words in the file named filename and returns the root of a BST with these words, ordered lexicographically, as keys and, for each key, a list of lines in which the word appears, as value.
    """
    i=0
    with open(filename) as inf:
        l=split_in_words_and_lowercase(inf.readline())
        tree=Node(l[0],[1],None,None)
    with open(filename) as infile:
        for line in infile:
            if i>len(filename):
                break
            a=split_in_words_and_lowercase(line)
            for k in a:
                tree.add(k,i+1)
            i+=1
    return tree

       
def example_bst():
    """
    defines the BST in a figure (the example ) and returns its root node:
    """
    n7 = Node(7,"Seven",None,None)
    n6 = Node(6,"Six", None,n7)
    n3 = Node(3,"Three",None,None)
    n4 = Node(4,"Four",n3,n6)
    n13 = Node(13,"Thirteen",None,None)
    n14 = Node(14,"Fourteen",n13,None)
    n10 = Node(10,"Ten",None,n14)
    n8 = Node(8,"Eight",n4,n10)
    return n8
def generate_index(textfile, indexfile):
    """
    constructs an index BST for the file named textfile and then writes the sorted index to a file indexfile.
    """
    a=construct_bst_for_indexing(textfile)
    b=a.write_in_order(indexfile)

def balanced_bst(sorted_list):
    """Return balanced BST constructed from sorted list."""
    return balanced_bst_rec(sorted_list, 0, len(sorted_list))

def balanced_bst_rec(sorted_list, lower, upper):
    """Recursive helper function for balanced_bst."""
    mid= (lower+upper)//2
    if lower == upper or lower +1 == upper:
        n=Node(sorted_list[lower][0],sorted_list[lower][1],None,None)
        return n
    else:
        n = Node(sorted_list[mid][0], sorted_list[mid][1],None,None)
        if  lower +2 ==upper:
            n.left= balanced_bst_rec(sorted_list, lower, mid)
        else:
            n.right= balanced_bst_rec(sorted_list, mid +1, upper)
            n.left= balanced_bst_rec(sorted_list, lower, mid)
    return n
            
        
    
    
    
    
    
    
        

