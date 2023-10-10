from math import log, log2
from random import randint

def getMid(start, stop):
    return start + (stop - start + 1) // 2

## Question 1
# Return frequency of v in L[start:stop].
# The worst-case run time is: O(n)
# Because: We iterate once over L.
def getFrequency(v, L, start, stop):
    freq = 0
    for i in range(start, stop):
        if L[i] == v:
            freq += 1
    return freq


## Question 2
# Return majority element of L if it exists, otherwise 'False'.
# The worst-case run time is: O(n²)
# Because: We call getFrequency for each element (at most) once.
def getMajorityNaively(L):
    n = len(L)
    for v in L:
        if getFrequency(v, L, 0, n) > n / 2:
            return v
    return False


## Question 3
# Return majority element of L if it exists, otherwise 'False'.
# The worst-case run time is: O(n log(n))
# Because: The function follows the recursion T(n) = 2T(n/2) + Θ(n).
def getMajorityDaC(L):
    def helpGetMajorityDaC(start, stop):
        if start + 1 == stop:
            return L[start]

        mid = getMid(start, stop)
        mLeft = helpGetMajorityDaC(start, mid)
        mRight = helpGetMajorityDaC(mid, stop)
        freqLeft = getFrequency(mLeft, L, start, stop)
        freqRight = getFrequency(mRight, L, start, stop)

        if freqRight > freqLeft:
            return mRight
        return mLeft

    n = len(L)
    cand = helpGetMajorityDaC(0, n)
    if getFrequency(cand, L, 0, n) > n / 2:
        return cand
    return False


## Question 4
# Return majority element of M if it exists, otherwise 'False'.
# The worst-case run time is: O(n log(n)) = O(n k)
# Because: The function follows the recursion T(n) = 4T(n/4) + Θ(n).
def getMajorityInMatrixDaC(M):
    def helpGetMajorityDaC(rowStart, rowStop, colStart, colStop):
        if (rowStart + 1 == rowStop) and (colStart + 1 == colStop):
            return M[rowStart][colStart]

        rowMid = getMid(rowStart, rowStop)
        colMid = getMid(colStart, colStop)

        mTopLeft = helpGetMajorityDaC(rowStart, rowMid, colStart, colMid)
        mTopRight = helpGetMajorityDaC(rowStart, rowMid, colMid, colStop)
        mBotLeft = helpGetMajorityDaC(rowMid, rowStop, colStart, colMid)
        mBotRight = helpGetMajorityDaC(rowMid, rowStop, colMid, colStop)

        freqTopLeft = getFrequencyFromMatrix(mTopLeft, M, rowStart, rowStop, colStart, colStop)
        freqTopRight = getFrequencyFromMatrix(mTopRight, M, rowStart, rowStop, colStart, colStop)
        freqBotLeft = getFrequencyFromMatrix(mBotLeft, M, rowStart, rowStop, colStart, colStop)
        freqBotRight = getFrequencyFromMatrix(mBotRight, M, rowStart, rowStop, colStart, colStop)

        winner = max(freqTopLeft, freqTopRight, freqBotLeft, freqBotRight)
        if winner == freqTopRight:
            return mTopRight
        if winner == freqBotLeft:
            return mBotLeft
        if winner == freqBotRight:
            return mBotRight
        return mTopLeft

    n = len(M)
    cand = helpGetMajorityDaC(0, n, 0, n)
    if getFrequencyFromMatrix(cand, M, 0, n, 0, n) > n * n / 2:
        return cand
    return False

# Returns the frequency of v in M[rowStart:rowStop][colStart:colStop].
def getFrequencyFromMatrix(v, M, rowStart, rowStop, colStart, colStop):
    freq = 0
    for row in range(rowStart, rowStop):
        freq += getFrequency(v, M[row], colStart, colStop)
    return freq


## Question 5
# Return majority element of L if it exists, otherwise 'False'.
# The worst-case run time is: O(n)
# Because: We iterate twice over L.
def getMajorityBoyerMoore(L):
    curr = None
    freq = 0
    for v in L:
        if freq == 0:
            curr = v
            freq += 1
        elif v != curr:
            freq -= 1
        else:
            freq += 1
    n = len(L)
    if getFrequency(curr, L, 0, n) > n / 2:
        return curr
    return False


## Question 6
# Return majority element of L with probability at least p if it exists, otherwise 'False'.
# Probability for one try finding the existing majority element is at least: 1/2
# Probability that m tries all fail (assuming a majority element exists) is at most: (1/2)^m
def getMajorityRandomized(L, p):
    tries = int(log2(1 / (1 - p)))
    n = len(L)
    for _ in range(tries):
        v = L[randint(0, n - 1)]
        freq = getFrequency(v, L, 0, n)
        if freq > n / 2:
            return v
    return False