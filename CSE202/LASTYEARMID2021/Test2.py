import numpy as np
import random
import math


def inverse(A):
    C = [[0 for i in range(len(A))] for j in range(len(A))]
    for i in range(len(A)):
        for j in range(len(A)):
            C[i][j] = -A[i][j]
    return C


def multiply_matrices(A, B):
    X = np.array(A)
    Y = np.array(B)
    Z = np.matmul(X, Y)
    return Z.tolist()


def compute_witness_trivial(A, B):
    W = [[0 for _ in range(len(A))] for _ in range(len(A))]
    for i in range(len(A)):
        for j in range(len(B)):
            for k in range(len(A)):
                if A[i][k] == B[k][j] and A[i][k] == 1:
                    W[i][j] = k+1
    return W

# Complexity=O(n^3)


def expose(A):
    Ahat = [[0 for _ in range(len(A))] for _ in range(len(A))]
    for i in range(len(A)):
        for j in range(len(A[0])):
            Ahat[i][j] = (j+1)*A[i][j]
    return Ahat


def compute_witness_unique(A, B):
    return multiply_matrices(expose(A), B)

# Complexity=O(n^3)


def nullify_columns(A, R):
    W = [[0 for _ in range(len(A))] for _ in range(len(A))]
    r = set(R)
    for i in range(len(A)):
        for j in r:
            W[i][j-1] = A[i][j-1]
    return W


def nullify_rows(A, R):
    W = [[0 for _ in range(len(A))] for _ in range(len(A))]
    r = set(R)
    for j in range(len(A)):
        for i in r:
            W[i-1][j] = A[i-1][j]
    return W


def compute_witness_restricted(A, B, R):
    return multiply_matrices(expose(nullify_columns(A, R)), nullify_rows(B, R))
# O(n^3)

# probablity of failing= 1-(1/2e)
# Probablity of failing after (2*e*log(n)) tries is: (1/2e)^(2*e*log(n))


def sample(r, n):
    X = [i+1 for i in range(n)]
    for i in range(len(X)):
        j = random.randint(i, n-1)
        v = X[i]
        X[i] = X[j]
        X[j] = v
    return X[:r]


def compute_witness_random(A, B):
    n = len(A)
    W = multiply_matrices(inverse(A), B)
    for t in range(int(math.log(n))+1):
        r = 2**t
        for i in range(int(2*math.e*math.log(n))):
            s = sample(r, n)
            Wr = compute_witness_restricted(A, B, s)
            for p in range(n):
                for q in range(n):
                    k = Wr[p][q]-1
                    print(k)
                    if W[p][q] < 0 and A[p][k] == B[k][q] and A[p][k] == 1:
                        W[p][q] = Wr[p][q]
    for i in range(n):
        for j in range(n):
            if W[i][j] < 0:
                W[i][j]=compute_witness_trivial(A,B)[i][j]
    return W
