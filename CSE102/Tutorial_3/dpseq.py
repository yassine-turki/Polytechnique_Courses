def next_seq(alphas,us):
    a=0
    for i in range(len(alphas)):
        a+=alphas[i]*us[i]
    return a
def u(alphas, us, n):
    for i in range(n):
        us = us[1:] + [next_seq(alphas, us)]
    return us[0]