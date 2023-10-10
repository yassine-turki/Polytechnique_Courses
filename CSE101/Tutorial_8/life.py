class Point:
    """Encodes a live point in the Game of Life.
    Data attributes:
    x -- x-coordinate
    y -- y-coordinate
    """

    def __init__(self, x, y):
        self.x = x
        self.y = y  
    def __repr__(self):
        return f'Point({self.x}, {self.y})'
    def __eq__(self, other):
        return (self.x == other.x) and (self.y == other.y)
    def __hash__(self):
        return hash((self.x,self.y))
    def get_neighbors(self):
        """Return the neighbors of the Point as a set."""
        s=set(Point(x,y) for x in range(self.x-1,self.x+2) for y in range(self.y-1, self.y+2))
        s.discard(self)
        return s
    
        

class Board:
    """A board to play the Game of Life on.
    Data attributes:
    points -- a set of Points
    x_size  -- size in x-direction
    y_size  -- size in y-direction
    """

    def __init__(self, x_size, y_size, points):
        self.points = points
        self.x_size = x_size
        self.y_size = y_size
        
    def is_legal(self, point):
        """Check if a given Point is on the board."""
        if 0<point.x < self.x_size and 0<point.y < self.y_size or (point.x==0 and point.y==0) :
            return True
        else:
            return False
        
    def number_live_neighbors(self, p):
        """Compute the number of live neighbors of p on the Board."""
        s=self.points
        return len(s.intersection(p.get_neighbors()))
    
    def next_step(self):
        """Compute the points alive in the next round and update the
        points of the Board.
        """
        new_set=set()
        for x in range(self.x_size):
            for y in range(self.y_size):
                p=Point(x,y)
                neighbours=self.number_live_neighbors(p)
                if neighbours>1:
                    if p in self.points and (neighbours==3 or neighbours==2):
                        new_set.add(p)
                    if p not in self.points and neighbours==3:
                        new_set.add(p)
        self.points=new_set
            
            
        
            
                
    def load_from_file(self, filename):
        """Load a board configuration from file in the following format:
        - The first two lines contain a number representing the size in
            x- and y-coordinates, respectively.
        - Each of the following lines gives the coordinates of a single
            point, with the two coordinate values separated by a comma.
            Those are the points that are alive on the board.
        """
        s=set()
        with open(filename,'r') as infile:
            x=infile.readline()
            self.x_size=int(x)
            y=infile.readline()
            self.y_size=int(y)
            r=infile.readlines()
            for c in r:
                p=Point(int(c[:c.index(',')]),int(c[c.index(',')+1:]))
                s.add(p)
        self.points=s
            
            
    
    
    def toggle_point(self, x, y):
        """Add Point(x,y) if it is not in points, otherwise delete it
        from points.
        """
        if Point(x,y) not in self.points:
            self.points.add(Point(x,y))
        else:
            self.points.discard(Point(x,y))
            
def is_periodic(board):
    """
    Return (True, 0) if the input board is periodic, otherwise (False, i),
    where i is the smallest index of the state to which it loops
    """
    # creer set copie de b
    s=[]
    s.append(board.points)
    for i in range(2**(board.x_size*board.y_size)):
        board.next_step()
        if board.points in s:
            if s.index(board.points)==0:
                return (True,0)
            else:
                return (False,i)
        s.append(board.points)
            
            
    
                
                

            
    
            
                
        
    
        
         
        