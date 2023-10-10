# -*- coding: utf-8 -*-
from uf import Rank_UF
import random

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
        self.player = 0


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
        
        pid = 1 if self.player == 1 else 2

        L = []        
        for k in [-1, 1]:
            if self.board[i+k][j] == pid:
                L.append([i+k,j])
            if self.board[i][j+k] == pid:
                L.append([i,j+k])
            if self.board[i+k][j-k] == pid:
                L.append([i+k,j-k])
        return L
    
    def is_game_over(self):
        '''
            TO IMPLEMENT
        '''
        if self.player == 1 and self.uf.is_connected(self.bot1, self.top1):
            print("Player 1 wins !")
            return True
            
        if self.player == 2 and self.uf.is_connected(self.bot2, self.top2):
            print("Player 2 wins !")
            return True

        return False

    def random_turn(self):
        '''
            TO IMPLEMENT
        '''
        idp = 1 if self.player == 1 else 2
        # chose random
        i, j = random.randint(1, self.size-2),random.randint(1, self.size-2)
        while self.board[i][j] != 0:
            i, j = random.randint(1, self.size-2),random.randint(1, self.size-2)
             
        self.board[i][j] = idp
        for p in self.neighbours(i,j):
            self.uf.union(self.hex_to_int(i,j), self.hex_to_int(p[0],p[1]))
        
    def random_play(self):
        '''
            TO IMPLEMENT
        '''
        
        num_turn = 0
        game_over = False
        while not game_over:
            self.random_turn()
            num_turn += 1
            
            game_over = self.is_game_over()
            
            self.player = 1 - self.player
            
        return num_turn/(self.size-2)**2
    


h = Hex(6)
r = h.random_play()
h.print_board()
print(r)
h.print_table2()