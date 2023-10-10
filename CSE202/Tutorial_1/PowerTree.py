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
        if k not in self.parent: 
            return -1
        a=[k]
        while(k!=1):
            k=self.parent[k]	
            a+=[k]
        return a
    
    def add_layer(self):
        l1 = self.layers[-1]
        l2=[]	
        for i in l1:
            path=self.path_from_root(i)
            for j in path:
               if i+j not in self.parent:
                   l2.append(i+j)
                   self.parent[i+j]=i
        self.layers.append(l2)
  
  