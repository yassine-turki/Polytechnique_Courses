from nfa import *

Black  = "\033[30m"
Red    = "\033[31m"
Green  = "\033[32m"
Yellow = "\033[33m"
Blue   = "\033[34m"

def test1():
    def performTests(regexes, argLists):
        for i, regex in enumerate(regexes):
            nfa = NFA(regex)
            # clear lp/rp because of match_*_or
            nfa.lp = [-1 for _ in range(len(nfa.s))]
            nfa.rp = [-1 for _ in range(len(nfa.s))]
            nfa.left_right_match()
            if nfa.lp  == [-1 for _ in range(len(nfa.s))]:
                print(f"  {Yellow}Skipping. Not implemented{Black}\n")
                return
            exp_lp = argLists[i][0]
            exp_rp = argLists[i][1]
            if nfa.lp == exp_lp and nfa.rp == exp_rp:
                print(f"  {Green}Success{Black} on: {regex}")
            else:
                print(f"  {Red}Error{Black} for: {regex}")
                print("  Expected:")
                print("    lp = " + str(exp_lp))
                print("    rp = " + str(exp_rp))
                print("  Obtained:")
                print("    lp = " + str(nfa.lp))
                print("    rp = " + str(nfa.rp) + '\n')
                return
        print()

    print(f"Testing {Blue}left_right_match{Black}.")
    nfa = NFA("(a)*")
    # clear lp/rp because of match_*_or
    nfa.lp = [-1 for _ in range(len(nfa.s))]
    nfa.rp = [-1 for _ in range(len(nfa.s))]
    nfa.left_right_match()
    if nfa.lp  == [-1 for _ in range(len(nfa.s))]:
        print(f"  {Yellow}Skipping. Not implemented{Black}\n")
        return

    performTests(
        ["(a)*b(c|(f|(e|g))*)*a", "(((a)*b)*c)*", "(((a|b)|c)|d)"],
        [
            [
                [-1, -1, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 11, 8, -1, 5, -1, -1],
                [2, -1, -1, -1, -1, 18, -1, -1, 16, -1, -1, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1]
            ],
            [
                [-1, -1, -1, -1, 2, -1, -1, 1, -1, -1, 0, -1],
                [10, 7, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1]
            ],
            [
                [-1, -1, -1, -1, -1, -1, 2, -1, -1, 1, -1, -1, 0],
                [12, 9, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]
            ]
        ]
    )

def test2():
    def performTests(regexes, argLists):
        for i, regex in enumerate(regexes):
            nfa = NFA(regex)
            exp_lp = argLists[i][0]
            exp_rp = argLists[i][1]
            if nfa.lp == exp_lp and nfa.rp == exp_rp:
                print(f"  {Green}Success{Black} on: {regex}")
            else:
                print(f"  {Red}Error{Black} for: {regex}")
                print("  Expected:")
                print("    lp = " + str(exp_lp))
                print("    rp = " + str(exp_rp))
                print("  Obtained:")
                print("    lp = " + str(nfa.lp))
                print("    rp = " + str(nfa.rp) + '\n')
                return
        print()

    print(f"Testing {Blue}left_right_match_or{Black}.")
    nfa = NFA("(a)*")
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print(f"  {Yellow}Skipping. Not implemented{Black}\n")
        return

    performTests(
        ["(a)*b(c|(f|(e|g))*)*a", "(((a)*b)*c)*", "(((a|b)|c)|d)"],
        [
            [
                [-1, -1, 0, -1, -1, -1, -1, 5, -1, -1, 8, -1, -1, 11, -1, 11, 8, -1, 5, -1, -1],
                [2, -1, -1, -1, -1, 18, -1, 18, 16, -1, 16, 15, -1, 15, -1, -1, -1, -1, -1, -1, -1]
            ],
            [
                [-1, -1, -1, -1, 2, -1, -1, 1, -1, -1, 0, -1],
                [10, 7, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1]
            ],
            [
                [-1, -1, -1, -1, 2, -1, 2, 1, -1, 1, 0, -1, 0],
                [12, 9, 6, -1, 6, -1, -1, 9, -1, -1, 12, -1, -1]
            ]
        ]
    )

def test3():
    def performTests(regexes, linkLists):
        for i, regex in enumerate(regexes):
            nfa = NFA(regex)
            exp_links = linkLists[i]
            for idx, links in enumerate(exp_links):
                exp = sorted(links)
                res = sorted(nfa.dg.neigh[idx])
                if exp != res:
                    print("  {}Error{}: {} is expected to be linked to {} but is linked to {}.\n".format(Red, Black, idx, exp, res))
                    return
            print(f"  {Green}Success{Black} on: {regex}")
        print()

    print(f"Testing {Blue}build_eps_links{Black}.")
    nfa=NFA("(a)*")
    if nfa.dg.neigh == [[] for _ in range(len(nfa.dg.neigh))]:
        print(f"  {Yellow}Skipping. Not implemented{Black}\n")
        return

    performTests(
        ["c(.(a|b))*k(.)*", "(b|c).(.(a|b))*c(.)*"],
        [
            [[], [9, 2], [], [6, 4], [], [7], [], [8], [9], [1, 10], [], [14, 12], [], [14], [11, 15], []],
            [[1, 3], [], [4], [], [5], [], [7, 14], [], [9, 11], [], [12], [], [13], [14], [15, 6], [], [17, 19], [], [19], [20, 16], []]
        ]
    )

def test4():
    print(f"Testing {Blue}check_text{Black}.")
    nfa = NFA("c(.(a|b))*k(.)*")
    if nfa.check_text("") is None:
        print(f"  {Yellow}Skipping. Not implemented{Black}\n")
        return
    for (s, expected) in [("", False), ("ck",True), ("cxak", True), ("cxck", False), ("cxak", True), ("cxaybzakzzzzzzz", True), ("cxaybza", False)]:
        output = nfa.check_text(s)
        if output != expected:
            print("  {}Error{} on word {}: expected {} but got {}".format(Red, Black, s, expected, output))
            return
    print(f"  {Green}Success{Black}!\n")

def test5():
    print(f"Testing {Blue}contains_pattern{Black}.")
    if contains_pattern("a", "a") is None:
        print(f"  {Yellow}Skipping. Not implemented{Black}\n")
        return
    pattern = "a(.)*a"
    for (s, expected) in [("", False), ("aa", True), ("aaa", True), ("baab", True), ("ba", False), ("a", False), ("dfhjkdghdkalgkjdfkgjdkjghalkdgjdlkgj", True)]:
        output = contains_pattern(pattern, s)
        if output != expected:
            print("  {}Error{} for pattern {} on word {}: expected {} but got {}".format(Red, Black, pattern, s, expected, output))
            return
    print(f"  {Green}Success{Black}!")

## Run tests
test1() # Question 1
test2() # Question 2
test3() # Question 3
test4() # Question 4
test5() # Question 5
