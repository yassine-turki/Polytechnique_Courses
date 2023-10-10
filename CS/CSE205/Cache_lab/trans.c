/* 
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1tB direct mapped cache with a bloct size of 32 bytes.
 */ 

//Name: Yassine Turti
//User Id: yassine.turti


#include <stdio.h>
#include "cachelab.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. 
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{

    int i, j, ii, jj, t, d; 

    if (N == 32) {  // We have a 32x32 matrix, so we can use a 8x8 block size and handle the diagonal separately to avoid conflict misses
        for (j = 0; j < M; j += 8) {
            for (i = 0; i < N; i += 8) {
                for (ii = i; ii < i + 8; ii++) {
                    for (jj = j; jj < j + 8; jj++) {
                        if (ii != jj) { //If not on the diagonal
                            B[jj][ii] = A[ii][jj];
                        } else { //Avoiding conflict misses
                            t = A[ii][jj];
                            d = ii;
                        }
                    }
                    if (i == j) { //If on the diagonal
                        B[d][d] = t;
                    }
                }
            }
        }
    }

    else if (M == 61) { // We have a 61x67 matrix, so we can use a 16x16 block size and handle the diagonal separately to avoid conflict misses

    for (i = 0; i < N; i += 16) {
        for (j = 0; j < M; j += 16) {
            
            for (ii = i; ii < i + 16 && ii < N; ++ii) {
                for (jj = j; jj < j + 16 && jj < M; ++jj) {
                    if (jj != ii) { //again, if not on the diagonal
                        B[jj][ii] = A[ii][jj];
                    } else { //Avoiding conflict misses on the diagonal
                        t = A[ii][jj];
                        B[jj][ii] = t;
                    }
                }
            }
        }
    }
}

else { 
        // Case 64x64 : in this case, we can only store 4 rows of the matrix in the cache, 
        // so we need to copy the next block to the cache before writing it to the matrix.
        // This also means we need to handle the last elements of the matrix separately to avoid conflict misses.

        int iii, jjj;
        for (j = 0; j < M; j += 8) {
            for (i = 0; i < N; i += 8) {
                ii = i;
                jj = j;
                iii = ii + 8;
                jjj = jj;
                jjj += (iii >= M) ? 8 : 0; // Check if the next block exceeds matrix size M
                iii -= (iii >= M) ? M : 0; // Adjust the next block index if it exceeds matrix size M

                while (j == iii) { // Loop until the next block index is different from j
                    iii += 8; // Increment the next block index by 8
                    if (iii >= M) { // If the next block index exceeds matrix size M
                        jjj += 8; // Increment the current block index by 8
                        iii -= M; // Adjust the next block index within the matrix size M
                    }
                }

                if (jjj < M) { // Check if the current block is within the matrix size M
                    int temp1 = iii + 8;
                    int temp2 = jjj;
                    temp2 += (temp1 >= M) ? 8 : 0; // Check if the next block exceeds matrix size M
                    temp1 -= (temp1 >= M) ? M : 0; // Adjust the next block index if it exceeds matrix size M

                    while (temp1 == j) { // Loop until the next block index is different from j
                        temp1 += 8; 
                        if (temp1 >= N) { 
                            temp2 += 8; 
                            temp1 -= N; // Adjust the next block index within the matrix size N
                        }
                    }

                    for (t = 0; t < 4; t++) { 
                        for (d = 0; d < 8; d++) {
                            B[temp2 + t][temp1 + d] = A[i + 4 + t][j + d];
                        }
                    }

                    for (t = 0; t < 4; t++) { 
                        for (d = 0; d < 8; d++) {
                            B[jjj + t][iii + d] = A[i + t][j + d]; 
                        }
                    }

                    for (t = 0; t < 4; t++) { 
                        for (d = 0; d < 4; d++) {
                            B[jj + d][ii + t] = B[jjj + t][iii + d];
                            B[jj + d][ii + 4 + t] = B[temp2 + t][temp1 + d]; 
                        }
                    }

                    for (t = 0; t < 4; t++) { 
                        for (d = 0; d < 4; d++) {
                            B[jj + 4 + d][ii + t] = B[jjj + t][iii + 4 + d];
                            B[jj + 4 + d][ii + 4 + t] = B[temp2 + t][temp1 + 4 + d];
                        }
                    }

                } 
                else { //else, we are at the last elements of the matrix, so we can just copy the block to the matrix
                    for (t = 0; t < 8; t++) {
                        for (d = 0; d < 8; d++) {
                            B[jj + d][ii + t] = A[i + t][j + d];
                        }
                    }
                }
            }
        }

} 
    }





/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple ii-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    // registerTransFunction(trans, trans_desc); 

}

/* 
 * is_transpose - This helper function chects if B is the transpose of
 *     A. You can chect the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

