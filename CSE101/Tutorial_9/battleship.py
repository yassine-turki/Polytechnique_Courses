import random
# List of tuples: (name, length) where length is the number of positions of your ship
ship_types = [('Battleship',4),('Carrier',5),('Cruiser',3),('Destroyer',2),('Submarine',3)]

class Ship:
    """A ship that can be placed on the grid."""

    def __repr__(self):
        return f"Ship('{self.name}', {self.positions})"

    def __str__(self):
        return f'{repr(self)} with hits {self.hits}'

    def __init__(self, name, positions):
        self.name=name
        self.positions=positions
        self.hits=set()
    def __eq__(self, other):
        return (self.name == other.name) and (self.positions == other.positions) and (self.hits == other.hits)
    def is_afloat(self):
        return(self.positions != self.hits)
    def take_shot(self, shot):
       """Check if the shot hits the ship. If so, remember the hit.
       Returns one of 'MISS', 'HIT', or 'DESTROYED'.
       """
       p=set()
       for s in self.positions:
           p.add(s)
       if shot in self.hits:
           return 'MISS'
       for i in self.hits:
           if i in p:
               p.remove(i)
       if shot in p and shot not in self.hits:
           self.hits.add(shot)
           p.remove(shot)
           if p==set():
               return 'DESTROYED'
           else:
               return 'HIT'
       else:
            return 'MISS'
       
     
    
class Grid:
    """Encodes the grid on which the Ships are placed.
    Also remembers the shots fired that missed all of the Ships.
    """
    
    def __init__(self, x_size, y_size):
        self.x_size = x_size
        self.y_size = y_size
        self.ships=[]
        self.misses=set()
        self.hits=set()
        self.sunken_ships=[]
        
        
    def add_ship(self, ship):
        """Add a Ship to the grid at the end of the ships list."""
        l=[]
        for n in ship.positions:
            for i in self.ships:
                if n in i.positions:
                    l.append(n)
        if len(l)==0:
            self.ships.append(ship)
            
    def shoot(self,position):
        if position in self.misses:
            return ('MISS', None)
        l=[]
        p=[]
        for s in self.ships:
            p.append(s)
        for i in self.ships:
            l.append(i.take_shot(position))
            if 'HIT' in l:
                self.hits.add(position)
                return ('HIT', None)
            elif 'DESTROYED' in l:
                self.sunken_ships.append(i)
                self.hits.add(position)
                return ('DESTROYED',p[p.index(i)])
        if 'HIT' not in l and 'DESTROYED' not in l:
            self.misses.add(position)
            return ('MISS',None)
        
    def random_ship(self):
        i=len(ship_types)
        s=ship_types[random.randint(0,i-1)]
        p=int(s[1])
        v=set()
        for n in range(p):
                v.add((random.randint(0,self.x_size),(random.randint(0,self.y_size))))
        self.ships.append(Ship(s[0],v))
        return Ship(s[0],v)
    def create_random(self,n):
        for i in range (n):
            self.random_ship()
        
        
class BlindGrid:
    """Encodes the opponent's view of the grid."""

    def __init__(self, grid):
        self.x_size=grid.x_size
        self.y_size=grid.y_size
        self.misses=grid.misses
        self.hits=grid.hits
        self.sunken_ships= grid.sunken_ships
            
    
def create_ship_from_line(line):
    l=line.split(' ')
            
    n=l[0]
    s=set()
    for i in range(1,len(l)):
        cut = l[i].index(':')
        s.add((int(l[i][:cut]),int(l[i][cut + 1:])))
    return Ship(n,s)

def load_grid_from_file(filename):
    with open(filename) as infile:
        a=infile.readline()
        l=[]
        cut = a.index(':')
        b=Grid(int(a[:cut]),int(a[cut + 1:]))
        for line in infile:
            s=create_ship_from_line(line)
            Grid.add_ship(b,s)
        return b
    
      
    