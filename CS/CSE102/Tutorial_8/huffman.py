import math

from heap import Heapq

def huffman_stats(s):
    stats = {}
    d=dict()
    for x in s:
        stats[x] = stats.get(x, 0) + 1
    for i,j in stats.items():
        d[i]=j/len(s)
    return d

class Node:
    def __init__(self, value, left = None, right = None):
        self.value = value
        self.left  = left
        self.right = right

def huffman_tree(d):
    if len(d) == 0:
        return None
    heap = Heap()
    for v, k in d.items():
        heap.push(Node(v), k)
    while len(heap) > 1:
        (n1, p1) = heap.pop()
        (n2, p2) = heap.pop()
        heap.push(Node(None, n1, n2), p1 + p2)
    return heap.pop()[0]