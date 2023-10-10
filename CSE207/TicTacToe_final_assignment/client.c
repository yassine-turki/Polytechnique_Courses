    #include <sys/types.h>
    #include <sys/socket.h>
    #include <netinet/in.h>
    #include <unistd.h>
    #include <netdb.h>
    #include <stdio.h>
    #include <string.h>
    #include <stdlib.h>
    #include <errno.h>
    #include <arpa/inet.h>

    #define FYI 0x01
    #define MYM 0x02
    #define END 0x03
    #define TXT 0x04
    #define MOV 0x05

    #define MAXBUFFERSIZE 1024

    void displayBoard(char game_board[3][3]) {
        printf("Current Board:\n");
        int i;
        for (i = 0; i < 3; i++) {
            printf("%c|%c|%c\n", game_board[i][0], game_board[i][1], game_board[i][2]);
            if (i != 2) {
                printf("-+-+-\n");
            }
        }
    }

    int main(int argc, char *argv[]) {
        // Check if IP address and port number are provided
        if (argc < 3) {
            printf("Please enter IP Address and Port number\n");
            return -1;
        }

        // Create a socket
        int sockfd = socket(AF_INET, SOCK_DGRAM, 0);
        if (sockfd == -1) {
            perror("socket");
            exit(-1);
        }

        const char* ip = argv[1];
        int port = atoi(argv[2]);
        struct sockaddr_in ipv4_address;
        memset(&ipv4_address, 0, sizeof(ipv4_address));
        ipv4_address.sin_family = AF_INET;
        ipv4_address.sin_port = htons(port);
        if (inet_pton(AF_INET, ip, &ipv4_address.sin_addr) <= 0) {
            perror("inet_pton");
            exit(-1);
        }

        char msg[7];
        msg[0] = TXT;
        strcpy(&msg[1], "Hello");
        socklen_t tolen = sizeof(ipv4_address);

        // Signal the server that the client is ready to play
        int sent = sendto(sockfd, &msg, sizeof(msg), 0, (struct sockaddr*)&ipv4_address, tolen);
        if (sent == -1) {
            perror("sendto");
            exit(-1);
        }

        char answer[MAXBUFFERSIZE]; // answer will store the server's response
        while (1) { 
            // Receive the server's response
            struct sockaddr_in from;
            socklen_t fromlen = sizeof(from);
            ssize_t received = recvfrom(sockfd, answer, MAXBUFFERSIZE, 0, (struct sockaddr*)&from, &fromlen);
            if (received == -1) {
                perror("recvfrom");
                exit(-1);
            }
            char message = answer[0];

            // Proceed according to the server's response 

            if (message == TXT) { // Text message, we print it
                puts(&answer[1]);
            }
            else if (message == MYM) { // Make your move
                answer[0] = MOV;
                int column, row;
                char input[10];
                while (1) {
                    printf("Enter column and row (values between 0 and 2): ");
                    fgets(input, sizeof(input), stdin);
                    if (sscanf(input, "%1d%1d", &column, &row) != 2 || (column < 0 || column > 2) || (row < 0 || row > 2)) {
                        puts("Invalid input. Please enter values between 0 and 2.");
                        continue;
                    }
                    break;
                    }
                answer[1] = column;
                answer[2] = row;
                int sent = sendto(sockfd, answer, 3, 0, (struct sockaddr*)&ipv4_address, tolen);
                if (sent == -1) {
                    perror("sendto");
                    exit(-1);
                }
                    }
            else if (message == END) { // Game over
                char winner = answer[1]; // Get the winner
                if (winner == 0) {
                    puts("DRAW!");
                }
                else if (winner == 1) {
                    puts("Winner: PLAYER 1!");
                }
                else if (winner == 2) {
                    puts("Winner: PLAYER 2!");
                }
                else if (winner == '\255') {
                    puts("Maxium games reached!");
                }
                close(sockfd);
                exit(EXIT_SUCCESS);
            }
            else if (message == FYI) { // For your information, display the game_board
                char game_board[3][3], move;
                int i, inc, row, col;
                memset(game_board, ' ', sizeof(game_board));

                for (i = 0; i < answer[1]; i++) {
                    inc = 2 + 3 * i;
                    if (answer[inc] == 1) {
                        move = 'X';
                    }   
                    else {
                        move = 'O';
                    }
                    row=(int)answer[inc + 2];
                    col=(int)answer[inc + 1];
                    game_board[row][col] = move;
                }
                displayBoard(game_board);
            }
            else {
                puts(answer);
            }
        }

        close(sockfd);
        return 0;
    }

