# How to start a game:

- Compile by using the "make" command
- Run the server executable along with a port number (e.g ./server 4000)
- For every game, open two new terminals and run two client executable with an IP Address and a port number as argument (e.g ./client 0.0.0.0 4000)
- The server accepts multiple games (limit defined by the macro MAX_GAMES), thus, we can accept multiple clients.
- To make a move, simply type the column number and the row number (both between 0 and 2). For example: 21 (for column 2, row 1)
- The server will notify the players of a winner or a draw when the game ends.