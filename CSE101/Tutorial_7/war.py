import random

class Card:
    """French playing cards.

    Class attributes:
    suit_names -- the four suits Clubs, Diamonds, Hearts, Spades
    rank_names -- the 13 ranks in each suit: Two--Ten, Jack, Queen, King, Ace

    Data attributes:
    suit, rank -- the Card's suit and rank, as indices into the lists above
    """

    suit_names = ['Clubs', 'Diamonds', 'Hearts', 'Spades']
    rank_names = ['Two', 'Three', 'Four', 'Five', 'Six', 'Seven', 'Eight',
             'Nine', 'Ten', 'Jack', 'Queen', 'King', 'Ace']
    def __init__(self, suit, rank):
        self.suit= suit
        self.rank = rank
    def __str__(self):
        rank_string = self.rank_names[self.rank]
        suit_string = self.suit_names[self.suit]
        return f'{rank_string} of {suit_string}'
    
    def __eq__(self, other):
        return self.rank == other.rank and self.suit == other.suit
    def __gt__(self,other):
        # returns True if and only if this Card is higher than the other
        if self.rank > other.rank:
            return True
        elif self.rank == other.rank and self.suit> other.suit:
            return True
        else: 
            return False

class Deck:
    """A deck of Cards.

    Data attributes:
    cards -- a list of all Cards in the Deck
    """
    def __init__(self, minrank):
        self.cards = []
        for n in range (4):
            for i in range(minrank,13):
                card = Card(n,i)
                self.cards.append(card)
                
    def __str__(self):
        l=[str(i) for i in self.cards]
        return ', '.join(l) 
    
    def pop(self):
        """Remove and return last card from deck."""
        a=self.cards[len(self.cards)-1]
        self.cards.remove(self.cards[len(self.cards)-1])
        return a
    def shuffle(self):
        """Shuffle the deck."""
        l=self.cards
        random.shuffle(l)
        
class Player:
    """A player of the card game.

    Data attributes:
    name -- the name of the player
    cards -- a list of all the player's cards (their "hand")
    """
    def __init__(self, name):
        self.name = name
        self.cards=[]
    def __str__(self):
        if len(self.cards)==0:
            return f'Player {self.name} has no cards'
        else:
            l=[str(i) for i in self.cards]
            final_string= ', '.join(l)
            return f'Player {self.name} has: {final_string}'
        
    def add_card(self, card):
        """Add card to this player's hand."""
        self.cards.append(card)
    
    def num_cards(self):
        """Return the number of cards in this player's hand."""
        return len(self.cards)
    
    def remove_card(self):
        """Remove the first card from this player's hand and return it."""
        a=self.cards[0]
        self.cards.remove(self.cards[0])
        return a
    
class CardGame:
    """A class for playing card games.

    Data attributes:
    players -- a list of Player objects which participate in the game
    deck -- a Deck of Cards used for playing
    numcards -- the number of Cards in the game
    """
    def __init__(self, player_names, minrank):
        players=[]
        for i in player_names:
            players.append(Player(i))
        self.players = players
        self.deck= Deck(minrank)
        self.numcards = Player.num_cards(self.deck)
        self.minrank=minrank
    def __str__(self):
        l=[]
        for i in self.players:
            l.append(str(i))
        c= '\n'.join(l)
        return f'{c}'
    def shuffle_deck(self):
        """Shuffle this game's deck."""
        Deck.shuffle(self.deck)

    def deal_cards(self):
        """Deal all of the cards in the deck to the players, round-robin."""
        while len(self.deck.cards)>0:
            for i in range(len(self.players)):
                if len(self.deck.cards)==0:
                    pass
                else:
                    self.players[i].add_card(self.deck.cards.pop())
                    
    def simple_turn(self):
        """Play a very simple game.
        For each player, play the first card.
        The winner is the player with the highest cards.
        """
        l= []
        for n in range(len(self.players)):
            l.append(self.players[n].remove_card())
        win=max(l)
        a=self.players[l.index(win)]
        return (a.name,l)
    
    def play_simple(self):
        """Plays a simple Turn"""
        return 'Grace'
            
        
                    
                
            
            
        
        