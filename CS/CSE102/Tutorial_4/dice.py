def win_probability(die1, die2):
    a=0
    for i in die1:
        for j in die2:
            if i>j:
                a+=1
    return a/len(die1)**2

def beats(die1, die2):
    return win_probability(die1, die2) > 0.5

def get_dice(n, s, dice):
    if len(dice) == n * s:
        if beats(dice[-s:], dice[:s]):
            yield dice
