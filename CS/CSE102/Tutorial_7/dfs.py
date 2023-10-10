

def required(G, c):
    stack=[c]
    visit=[]
    while stack:
        node = stack.pop()
        if node in visit:
            continue
        visit.append(node)
        for i in reversed(G[node]):
            stack.append(i)
    return len(visit)
        
def required_list(G, c):
    stack=[c]
    visit=[]
    while stack:
        node = stack.pop()
        if node in visit:
            continue
        visit.append(node)
        for i in reversed(G[node]):
            stack.append(i)
    return sorted(visit)
def reverse(graph):
      ans = [[] for _ in graph]
      for i, l in enumerate(graph):
         for x in l:
            ans[x].append(i)
      return ans
def needed_for(G, c):
    return required(reverse(G), c)

