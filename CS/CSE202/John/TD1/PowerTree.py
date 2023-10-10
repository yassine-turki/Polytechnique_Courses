# -*- coding: utf-8 -*-

class PowerTree:
    def __init__(self): 
        self.layers=[[1]]
        self.parent={1:1}
    
    def draw_tree(self):
        for i in range(len(self.layers)):	
            print("layer",i)
            for j in self.layers[i]: print(j,"->",self.parent[j])  
  	
    def path_from_root(self,k):
        path = [k]
        while k !=1:
            k = self.parent[k]
            path = [k] + path
        return path
    
    def add_layer(self):
        new_layer = []
        current_layer = self.layers[-1]
        for node in current_layer:
            path = self.path_from_root(node)
            for e in path:
                new_node = node+e
                
                if new_node not in self.parent:
                    new_layer.append(new_node)
                    self.parent[new_node] = node
        self.layers.append(new_layer)
  