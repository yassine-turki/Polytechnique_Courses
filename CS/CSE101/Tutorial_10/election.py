class Vote:
    """A single vote object.
    
    Data attributes:
    - preference_list: a list of the preferred parties for this voter,
      in descending order of preference.
    """
    def __init__(self, preference_list):
        self.preference_list=preference_list
    def __str__(self):
        if self.preference_list==[]:
            return 'Blank'
        else:
            return ' > '.join(self.preference_list)
    def __repr__(self):
        return f"Vote({self.preference_list})"
    
    def first_preference(self):
        if self.preference_list==[]:
            return None
        else:
            return self.preference_list[0]
        
    def preference(self, names):
        """Return the item in names that occurs first in the preference list,
        or None if no item in names appears.
        """
        for vote in self.preference_list:
            if vote in names:
                return vote
        return None
        
        
        
class Election:
    """A basic election class.
    
    Data attributes:
    - parties: a list of party names
    - blank: a list of blank votes
    - piles: a dictionary with party names for keys
      and lists of votes (allocated to the parties) for values
    - dead: a list with eliminated paties
    """
    
    def __init__(self, parties):
        self.parties = parties
        self.blank = []
        self.piles = {name:[] for name in self.parties}
        self.dead=[]
        
    def add_vote(self, vote):
        """Append the vote to the corresponding pile."""
        if len(vote.preference_list)==0:
            self.blank.append(vote)
        else:
            self.piles[vote.first_preference()].append(vote)
        
    def status(self):
        
      """Return the current status of the election:
      a dictionary mapping each of the party names in the piles
      to the number of votes in their pile.
      """
      v={}
      for k in self.piles:
          v[k]= len(self.piles[k])
      return v
    
    def add_votes_from_file(self, filename):
        """
        Convert each line of the file into a Vote,
        and append each of the votes to the correct pile.
        """
        
        with open(filename) as infile:
            v=infile.read().strip().split('\n')
            l=[line.strip().split(' ') for line in v]
        for i in l:
            if i==['']:
                self.blank.append(Vote([]))
            else:
                self.piles[i[0]].append(Vote(i))
                
    def first_past_the_post_winner(self):
        """Return the winner of this election under
        the first-past-the-post system, or None if
        the election is tied.
        """
        c=0
        d=0
        a=self.status().values()
        m=max(a)
        if m==0:
            return None
        for k in self.status():
            if self.status()[k]==m:
                    c=k 
                    break
        for l in self.status():
            if self.status()[l]==m:
                    d=l
        if c==d:
            return c
        else:
            return None
        
    def weighted_status(self):
        """Returns a dictionary with keys being the parties
        and values being the number of points (counted using
        the weighted scheme) that the party got.
        """
        v={'BLUE':0, 'PURPLE':0, 'WHITE':0, 'GREEN':0, 'RED':0}
        for k in self.piles:
            for vote in self.piles[k]:
                c=5
                for colour in vote.preference_list:   
                    v[colour] += c
                    c-=1
        return v
        

    def weighted_winner(self):
        """
        Return the winner of this election under
        the weighted voting scheme.
        """
        c=0
        d=0
        a=self.weighted_status().values()
        m=max(a)
        if m==0:
            return sorted(self.weighted_status())[0]
            
        for k in self.weighted_status():
            if self.weighted_status()[k]==m:
                    c=k 
                    break
        for l in self.weighted_status():
            if self.weighted_status()[l]==m:
                    d=l
        if c==d:
            return c
        else:
            return sorted(self.weighted_status())[0]
        
    def eliminate(self, party):
        """Remove the given party from piles, and redistribute its 
        votes among the parties not yet eliminated, according to 
        their preferences.  If all preferences have been eliminated, 
        then add the vote to the dead list.
        """
        parties = self.parties
        parties.remove(party)
        for v in self.piles[party]:
            if v.preference(parties) != None:
                self.piles[v.preference(parties)].append(v)
            else:
                self.dead.append(v)   
        self.piles.pop(party)
        
    def round_loser(self):
        """Return the name of the party to be eliminated from the next round."""
        l=[]
        parties=[k for k in self.piles]
        f=[]
        nl=[]
        fl=[]
        loser=[]
        for votes in self.piles.values():
            l.append(len(votes))
        mv=min(l)
        for votes in self.piles.values():
            if len(votes)== mv:
                    for v in votes:
                        nl.append(v.first_preference())
        if l.count(mv)==1:
                        for v in l:
                            if v==mv:
                                f.append(parties[l.index(v)])
                            print(l)
                            print(mv)
                            p=l.index(mv)
                            print(p)
                            return parties[p]
        else:
            for pile in self.piles:
                a=nl.count(pile)
                fl.append((a,pile))
            for numvote in fl:
                if numvote[0] != mv:
                    fl.remove(numvote)
            if len(fl)!=1:
                    t=[i[0] for i in fl]
                    print(f't={t}')
                    for g in fl:
                        if g[0]==min(t):
                            loser.append(g[1])
                            print(f'loser:{loser}') 
                            print(f'fl={fl}')
                
                    if len(loser)==1:
                        return loser[0]
                    else:
                        return sorted(loser)[0]
                
    
    def preferential_winner(self):
        """Run a preferential election based on the current piles of votes,
        and return the winning party.
        """
        while len(self.piles)!=1:
           self.eliminate(self.round_loser()) 
        l=[k for k in self.piles]
        return l[0]
            
            
            
        
        
            
        
            
            