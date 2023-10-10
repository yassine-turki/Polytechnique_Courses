#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <pthread.h>

#define FYI 0x01
#define MYM 0x02
#define END 0x03
#define TXT 0x04
#define MOV 0x05

#define MAXBUFFERSIZE 1024
#define MAX_GAMES 10

// create a struct to support multiple game boards
struct game_instance {
    struct sockaddr_in client_addr[2];
    char gameStatus[29];
    int game_board[3][3];
    int turn;
    int num_moves;
};

struct game_instance games[MAX_GAMES];

int find_player(struct sockaddr_in client) {
    int i;
    for (i = 0; i < 2 * MAX_GAMES; i++) {
        if (games[i / 2].client_addr[i % 2].sin_addr.s_addr == client.sin_addr.s_addr &&
            games[i / 2].client_addr[i % 2].sin_port == client.sin_port) {
            return i;
        }
    }
    return -1;
}

// Function to check for a winner
int checkWinner(int game_num) {
    // Check rows
    int i;
    for (i = 0; i < 3; i++) {
        if (games[game_num].game_board[i][0] != 0 &&
            games[game_num].game_board[i][0] == games[game_num].game_board[i][1] &&
            games[game_num].game_board[i][0] == games[game_num].game_board[i][2]) {
            return games[game_num].game_board[i][0];
        }

    }

    // Check columns
    for (i = 0; i < 3; i++) {
        if (games[game_num].game_board[0][i] != 0 &&
            games[game_num].game_board[0][i] == games[game_num].game_board[1][i] &&
            games[game_num].game_board[0][i] == games[game_num].game_board[2][i]) {
            return games[game_num].game_board[0][i];
        }
    }

    // Check diagonals
    if (games[game_num].game_board[0][0] != 0 && games[game_num].game_board[0][0] == games[game_num].game_board[1][1] &&
        games[game_num].game_board[0][0] == games[game_num].game_board[2][2]) {
        return games[game_num].game_board[0][0];
    }
    if (games[game_num].game_board[0][2] != 0 && games[game_num].game_board[0][2] == games[game_num].game_board[1][1] &&
        games[game_num].game_board[0][2] == games[game_num].game_board[2][0]) {
        return games[game_num].game_board[0][2];
    }

    return 0; // No winner
}

int main(int argc, char *argv[]) {

    // Argument check
    if (argc < 2) {
        printf("Please enter Port number\n");
        return -1;
    }

    // Socket creation + binding
    int sockfd = socket(AF_INET, SOCK_DGRAM, 0);
    if (sockfd == -1) { // If socket creation fails
        perror("socket");
        exit(-1);
    }

    int port = atoi(argv[1]); // Convert str to int

    struct sockaddr_in server_address;
    memset(&server_address, 0, sizeof(server_address));
    server_address.sin_family = AF_INET;
    server_address.sin_port = htons(port);
    server_address.sin_addr.s_addr = INADDR_ANY;

    int bind_result = bind(sockfd, (struct sockaddr *) &server_address, sizeof(server_address));
    if (bind_result == -1) {
        perror("bind");
        exit(-1);
    }

    // answer will store the message received from the client
    char answer[MAXBUFFERSIZE];
    int number_of_clients = 0; // How many clients are connected

    // initialize the game boards
    int i, j;
    for (i = 0; i < MAX_GAMES; i++) {
        for (j = 0; j < 3; j++) {
            games[i].game_board[j][0] = 0;
            games[i].game_board[j][1] = 0;
            games[i].game_board[j][2] = 0;
        }
        games[i].turn = 0;
        games[i].num_moves = 0;
        games[i].gameStatus[0] = FYI;
    }

    char first_msg[7];
    first_msg[0] = TXT;
    strcpy(&first_msg[1], "Hello");
    char message_to_p1[51];
    message_to_p1[0] = TXT;
    strcpy(message_to_p1, "Waiting for P2...");

    while (1) {
        struct sockaddr_in client;
        socklen_t fromlen = sizeof(client);
        ssize_t received = recvfrom(sockfd, answer, MAXBUFFERSIZE, 0, (struct sockaddr *) &client,
                                    &fromlen); //Message from client
        if (received == -1) {
            perror("recvfrom");
            exit(-1);
        }

        int global_index = find_player(client);
        int game_index = global_index / 2;
        int player = global_index % 2;

        // Check if the message by the clients corresponds to TXT Hello. If yes, we check if we add client to the game
        if (strcmp(answer, first_msg) == 0) {
            // Check the number of clients
            if (number_of_clients == 2 * MAX_GAMES) { // Too many clients, send END
                answer[0] = END;
                answer[1] = '\255';
                int sent = sendto(sockfd, answer, 2, 0, (struct sockaddr *) &client, sizeof(client));
                if (sent == -1) {
                    perror("sendto");
                    exit(-1);
                }
                continue;
            } else { // We can add the client to the game
                games[number_of_clients / 2].client_addr[number_of_clients % 2] = client;
                game_index = number_of_clients / 2;
                char msg[100];
                char x_o = (number_of_clients % 2 == 0) ? 'X' : 'O';
                sprintf(msg, "Welcome, you are player %d, you play with %c", ((number_of_clients)%2)+1, x_o);
                answer[0] = TXT;
                strncpy(answer + 1, msg, MAXBUFFERSIZE - 1);
                int sent = sendto(sockfd, answer, strlen(answer) + 1, 0,
                                  (struct sockaddr *) &games[number_of_clients / 2].client_addr[
                                          number_of_clients % 2],
                                  sizeof(games[number_of_clients / 2].client_addr[number_of_clients % 2]));
                if (sent == -1) {
                    perror("sendto");
                    exit(-1);
                }
                if (number_of_clients % 2 == 0) {
                    int sent = sendto(sockfd, message_to_p1, strlen(message_to_p1) + 1, 0,
                                      (struct sockaddr *) &games[number_of_clients / 2].client_addr[
                                              number_of_clients % 2],
                                      sizeof(games[number_of_clients / 2].client_addr[number_of_clients % 2]));
                    if (sent == -1) {
                        perror("sendto");
                        exit(-1);
                    }
                }
                number_of_clients += 1;
                if (number_of_clients % 2 == 1) {
                    continue;
                }
            }

        } else { // If the message is not Hello, we check if it is a MOV message

            if (games[game_index].turn == player) { // Check if it is the player's turn
                if (answer[0] != MOV) { //invalid
                    char msg[] = "Expected MOV message";
                    answer[0] = TXT;
                    strncpy(answer + 1, msg, MAXBUFFERSIZE - 1);
                    int sent = sendto(sockfd, answer, strlen(answer) + 1, 0, (struct sockaddr *) &client,
                                      sizeof(client));
                    if (sent == -1) {
                        perror("sendto");
                        exit(-1);
                    }
                } else { // MOV
                    int col = (int) answer[1]; //Convert the rows and column from char to int
                    int row = (int) answer[2];

                    if (games[game_index].game_board[col][row] != 0) { // If the cell is already filled
                        // Ask the player to re-input the cell positions
                        char msg[] = "Cell already filled, make another move";
                        answer[0] = TXT;
                        strncpy(answer + 1, msg, MAXBUFFERSIZE - 1);
                        int sent = sendto(sockfd, answer, strlen(answer) + 1, 0,
                                          (struct sockaddr *) &games[game_index].client_addr[player],
                                          sizeof(games[game_index].client_addr[player]));
                        if (sent == -1) {
                            perror("sendto");
                            exit(-1);
                        }
                        answer[0] = MYM;
                        int sent2 = sendto(sockfd, answer, 3, 0,
                                           (struct sockaddr *) &games[game_index].client_addr[player],
                                           sizeof(games[game_index].client_addr[player]));
                        if (sent2 == -1) {
                            perror("sendto");
                            exit(-1);
                        }
                        continue;
                    } else { // If the cell is not filled
                        games[game_index].game_board[col][row] = player + 1;
                        int inc = 2 + 3 * games[game_index].num_moves;
                        games[game_index].gameStatus[inc] = (char) (player + 1);
                        games[game_index].gameStatus[inc + 1] = answer[1];
                        games[game_index].gameStatus[inc + 2] = answer[2];
                        games[game_index].num_moves += 1;
                        games[game_index].gameStatus[1] = games[game_index].num_moves;
                        // Send board to the players
                        int sent1 = sendto(sockfd, games[game_index].gameStatus, sizeof(games[game_index].gameStatus),
                                           0,
                                           (struct sockaddr *) &games[game_index].client_addr[0],
                                           sizeof(games[game_index].client_addr[0]));
                        int sent2 = sendto(sockfd, games[game_index].gameStatus, sizeof(games[game_index].gameStatus),
                                           0,
                                           (struct sockaddr *) &games[game_index].client_addr[1],
                                           sizeof(games[game_index].client_addr[1]));
                        if (sent1 == -1 || sent2 == -1) {
                            perror("sendto");
                            exit(-1);
                        }
                    }
                    // Check if we have a win / draw
                    int winner = checkWinner(game_index);
                    answer[0] = END;
                    answer[1] = (char) winner;
                    if (winner > 0 ||
                        games[game_index].num_moves == 9) { // If the board is filled or we have a winner or a draw
                        if (winner == 0) {
                            answer[1] = '\0'; // Indicate a draw with a null character
                        }
                        // Send the winner/draw to the players
                        int sent1 = sendto(sockfd, answer, 2, 0, (struct sockaddr *) &games[game_index].client_addr[0],
                                           sizeof(games[game_index].client_addr[0]));
                        int sent2 = sendto(sockfd, answer, 2, 0, (struct sockaddr *) &games[game_index].client_addr[1],
                                           sizeof(games[game_index].client_addr[1]));
                        if (sent1 == -1 || sent2 == -1) {
                            perror("sendto");
                            exit(-1);
                        }
                        continue;
                    }
                    // Next player's turn
                    games[game_index].turn = (player == 0) ? 1 : 0;
                }
            } else {
                char msg[] = "Wrong access!";
                answer[0] = TXT;
                strncpy(answer + 1, msg, MAXBUFFERSIZE - 1);
                int sent = sendto(sockfd, answer, strlen(answer) + 1, 0, (struct sockaddr *) &client, sizeof(client));
                if (sent == -1) {
                    perror("sendto");
                    exit(-1);
                }
            }
        }
        // Send MYM Message to the next player
        answer[0] = MYM;
        int sent = sendto(sockfd, answer, 3, 0,
                          (struct sockaddr *) &games[game_index].client_addr[games[game_index].turn],
                          sizeof(games[game_index].client_addr[games[game_index].turn]));
        if (sent == -1) {
            perror("sendto");
            exit(-1);
        }
    }
    close(sockfd);
    return 0;
}

