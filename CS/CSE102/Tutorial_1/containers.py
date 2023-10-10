class Rdict:
    def __init__(self):
        self.__fwd= dict()
        self.__bwd= dict()
    @property        
    def fwd(self):
        return self.__fwd
    @property 
    def bwd(self):
        return self.__bwd
    def associate(self,a,b):
        if a not in self.fwd or b not in self.bwd:
            self.fwd[a]=b
            self.bwd[b]=a
    def __len__(self):
        return len(self.fwd)
    def __getitem__(self,k):
        (n,value)=k
        if n<0:
            if value in self.bwd:
                return self.bwd[value]
            else:
                return None
        if n>0:
            if value in self.fwd:
                return self.fwd[value]
            else:
                return None
    
    def __setitem__(self,k,v):
        (n,value)=k
        if n<0:
            self.bwd[value]=v
            self.fwd[v]=value
        if n>0:
            self.fwd[value]=v
            self.bwd[v]=value