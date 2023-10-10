# -*- coding: utf-8 -*-
from uf import Rank_UF
import random
import numpy as np

class Hex:
    def __init__(self, N):
        # size of the board (counting extra rows / columns)
        self.size = N+2
        # initialisation of the board (all hexagons are free)
        self.board = [[0 for j in range(self.size)] for i in range(self.size)]

        # initialisation of the Union-Find object
        nelem = self.size**2
        self.uf = Rank_UF(nelem)

        # first player to play is player 1
        self.player = 1


        l = self.size-1
        # union of sides of each player
        # player 1 is affected to the extra rows, player 2 extra columns
        for i in range(1,self.size-1):
            self.board[0][i] = 1
            self.board[l][i] = 1
            self.board[i][0] = 2
            self.board[i][l] = 2


            if i > 0:
                self.uf.union(self.hex_to_int(1,0), self.hex_to_int(i,0))
                self.uf.union(self.hex_to_int(1,l), self.hex_to_int(i,l))

                self.uf.union(self.hex_to_int(0,1), self.hex_to_int(0,i))
                self.uf.union(self.hex_to_int(l,1), self.hex_to_int(l,i))

        # get the indices in UF of the bottom and top sides of each player
        self.bot1 = self.hex_to_int(0,1)
        self.top1 = self.hex_to_int(l,1)
        self.bot2 = self.hex_to_int(1,0)
        self.top2 = self.hex_to_int(1,l)


    def hex_to_int(self, i, j):
        return i*(self.size) +j

    def print_board(self):
        for i in range(1, self.size-1):
            print(' '*(i-1),end='')
            for j in range(1, self.size-1):
                if self.board[i][j] == 0:
                    print('_', end='')
                if self.board[i][j] == 1:
                    print('X', end='')
                if self.board[i][j] == 2:
                    print('O', end='')
            print()


    def neighbours(self, i, j):
        '''
            TO IMPLEMENT
        '''
        
        p = 1 if self.player == 1 else 2
        l = []        
        for n in [-1, 1]:
            if self.board[i+n][j] == p:
                l.append([i+n,j])
            if self.board[i][j+n] == p:
                l.append([i,j+n])
            if self.board[i+n][j-n] == p:
                l.append([i+n,j-n])
        return l

    def is_game_over(self):
        p=self.player
        uf=self.uf
        if (p==1 and uf.find(self.top1) == uf.find(self.bot1)) or (p==2 and uf.find(self.top2)== uf.find(self.bot2)):
            print('Winner:',p)
            return True
        return False
        

    def random_turn(self):
        p=self.player
        i=random.randint(1,self.size-2)
        j=random.randint(1,self.size-2)
        while True:
            if self.board[i][j]!=0:
                i=random.randint(1,self.size-2)
                j=random.randint(1,self.size-2)
            else:
                break
        self.board[i][j]=p
        for neighbor in self.neighbours(i, j):
            self.uf.union(self.hex_to_int(i, j), self.hex_to_int(neighbor[0], neighbor[1]))

    def random_play(self):
        turns=0
        while True:
            turns+=1
            self.random_turn()
            if self.is_game_over(): break
            if self.player==1:
                self.player=2
            else:
                self.player=1
        return (turns)/(self.size-2)**2

def test():
    return np.mean([Hex(8).random_play() for i in range(200)])
test()          
HEX = Hex(8)
game=HEX.random_play()
HEX.print_board()
print(game)      
