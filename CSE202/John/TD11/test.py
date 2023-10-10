from NFA import *

grading_mode = True

def test1():
    print("testing left_right_match")
    nfa=NFA("(a)*b(c|(f|(e|g))*)*a")
    # clear lp/rp because of match_*_or
    nfa.lp=[-1 for _ in range(len(nfa.s))]
    nfa.rp=[-1 for _ in range(len(nfa.s))]
    nfa.left_right_match()
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print("Skipping left_right_match (unimplemented)")
        assert not grading_mode
        return
    exp_lp=[-1, -1, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 11, 8, -1, 5, -1, -1]
    exp_rp=[2, -1, -1, -1, -1, 18, -1, -1, 16, -1, -1, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1]
    if nfa.lp==exp_lp and nfa.rp==exp_rp:
        print("++ Success! on (a)*b(c|(f|(e|g))*)*a")
    else:
        print("!! Error for (a)*b(c|(f|(e|g))*)*a: expected")
        print("lp = "+ str(exp_lp))
        print("rp = "+ str(exp_rp))
        print("but obtained")
        print("lp = "+ str(nfa.lp))
        print("rp = "+ str(nfa.rp))
        assert not grading_mode
        
    nfa=NFA("(((a)*b)*c)*")
    # clear lp/rp because of match_*_or
    nfa.lp=[-1 for _ in range(len(nfa.s))]
    nfa.rp=[-1 for _ in range(len(nfa.s))]
    nfa.left_right_match()
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print("Skipping left_right_match (unimplemented)")
        assert not grading_mode
        return
    exp_lp=[-1, -1, -1, -1, 2, -1, -1, 1, -1, -1, 0, -1]
    exp_rp=[10, 7, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1]
    if nfa.lp==exp_lp and nfa.rp==exp_rp:
        print("++ Success! on (((a)*b)*c)*")
    else:
        print("!! Error for (((a)*b)*c)*: expected")
        print("lp = "+ str(exp_lp))
        print("rp = "+ str(exp_rp))
        print("but obtained")
        print(nfa.lp)
        print(nfa.rp)
        assert not grading_mode    
        
    nfa=NFA("(((a|b)|c)|d)")
    # clear lp/rp because of match_*_or
    nfa.lp=[-1 for _ in range(len(nfa.s))]
    nfa.rp=[-1 for _ in range(len(nfa.s))]
    nfa.left_right_match()
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print("Skipping left_right_match (unimplemented)")
        assert not grading_mode
        return
    exp_lp=[-1, -1, -1, -1, -1, -1, 2, -1, -1, 1, -1, -1, 0]
    exp_rp=[12, 9, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]
    if nfa.lp==exp_lp and nfa.rp==exp_rp:
        print("++ Success! on (((a|b)|c)|d)")
    else:
        print("!! Error for (((a|b)|c)|d): expected")
        print("lp = "+ str(exp_lp))
        print("rp = "+ str(exp_rp))
        print("but obtained")
        print(nfa.lp)
        print(nfa.rp)
        assert not grading_mode  
    

def test2():
    print("testing left_right_match_or")
    nfa=NFA("(a)*b(c|(f|(e|g))*)*a")
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print("Skipping left_right_match_or (unimplemented)")
        assert not grading_mode
        return
    exp_lp=[-1, -1, 0, -1, -1, -1, -1, 5, -1, -1, 8, -1, -1, 11, -1, 11, 8, -1, 5, -1, -1]
    exp_rp=[2, -1, -1, -1, -1, 18, -1, 18, 16, -1, 16, 15, -1, 15, -1, -1, -1, -1, -1, -1, -1]
    if nfa.lp==exp_lp and nfa.rp==exp_rp:
        print("++ Success! on (a)*b(c|(f|(e|g))*)*a")
    else:
        print("Error for (a)*b(c|(f|(e|g))*)*a: expected")
        print("lp = "+ str(exp_lp))
        print("rp = "+ str(exp_rp))
        print("but obtained")
        print(nfa.lp)
        print(nfa.rp)
        assert not grading_mode
        
    nfa=NFA("(((a)*b)*c)*")
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print("Skipping left_right_match_or (unimplemented)")
        assert not grading_mode
        return
    exp_lp=[-1, -1, -1, -1, 2, -1, -1, 1, -1, -1, 0, -1]
    exp_rp=[10, 7, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1]
    if nfa.lp==exp_lp and nfa.rp==exp_rp:
        print("++ Success! on (((a)*b)*c)*")
    else:
        print("!! Error for (((a)*b)*c)*: expected")
        print("lp = "+ str(exp_lp))
        print("rp = "+ str(exp_rp))
        print("but obtained")
        print(nfa.lp)
        print(nfa.rp)
        assert not grading_mode
        
    nfa=NFA("(((a|b)|c)|d)")
    if nfa.lp == [-1 for _ in range(len(nfa.s))]:
        print("Skipping left_right_match_or (unimplemented)")
        assert not grading_mode
        return
    exp_lp=[-1, -1, -1, -1, 2, -1, 2, 1, -1, 1, 0, -1, 0]
    exp_rp=[12, 9, 6, -1, 6, -1, -1, 9, -1, -1, 12, -1, -1]
    if nfa.lp==exp_lp and nfa.rp==exp_rp:
        print("++ Success! on (((a|b)|c)|d)")
    else:
        print("!! Error for (((a|b)|c)|d): expected")
        print("lp = "+ str(exp_lp))
        print("rp = "+ str(exp_rp))
        print("but obtained")
        print(nfa.lp)
        print(nfa.rp)
        assert not grading_mode       

def test3():
    print("testing build_eps_links")
    nfa=NFA("c(.(a|b))*k(.)*")
    if nfa.dg.neigh == [[] for _ in range(len(nfa.dg.neigh))]:
        print("Skipping build_eps_links (unimplemented)")
        assert not grading_mode
        return
    output=nfa.dg.to_string()
    expected=[[], [9, 2], [], [6, 4], [], [7], [], [8], [9], [1, 10], [], [14, 12], [], [14], [11, 15], []]
    for idx,links in enumerate(expected):
        exp = sorted(links)
        res = sorted(nfa.dg.neigh[idx])
        if exp != res:
            print("!! Error: {} is expected to be linked to {} but is linked to {}".format(idx, exp, res))
            assert not grading_mode
            return
    print("++ Success! on c(.(a|b))*k(.)*")


    nfa=NFA("(b|c).(.(a|b))*c(.)*")
    if nfa.dg.neigh == [[] for _ in range(len(nfa.dg.neigh))]:
        print("Skipping build_eps_links (unimplemented)")
        assert not grading_mode
        return
    output=nfa.dg.to_string()
    expected=[[1, 3], [], [4], [], [5], [], [7, 14], [], [9, 11], [], [12], [], [13], [14], [15, 6], [], [17, 19], [], [19], [20, 16], []]
    for idx,links in enumerate(expected):
        exp = sorted(links)
        res = sorted(nfa.dg.neigh[idx])
        if exp != res:
            print("!! Error: {} is expected to be linked to {} but is linked to {}".format(idx, exp, res))
            assert not grading_mode
            return
    print("++ Success! on (b|c).(.(a|b))*c(.)*")

def test4():
    print("testing check_text")
    nfa=NFA("c(.(a|b))*k(.)*")
    if nfa.check_text("") is None:
        print("Skipping check_text (unimplemented)")
        assert not grading_mode
        return
    for (s,expected) in [("", False), ("ck",True), ("cxak", True), ("cxck", False),
                         ("cxak", True), ("cxaybzakzzzzzzz", True), ("cxaybza", False)]:
        output = nfa.check_text(s)
        if output != expected:
            print("Error on word {}: expected {} but got {}".format(s, expected, output))
            assert not grading_mode
            return
    print("++ Success!")

def test5():
    print("testing contains_pattern")
    if contains_pattern("a", "a") is None:
        print("Skipping contains_pattern (unimplemented)")
        assert not grading_mode
        return
    pattern = "a(.)*a"
    for (s,expected) in [("", False), ("aa", True), ("aaa", True), ("baab", True),
                         ("ba", False), ("a", False), ("dfhjkdghdkalgkjdfkgjdkjghalkdgjdlkgj", True)]:
        output = contains_pattern(pattern, s)
        if output != expected:
            print("Error on word {}: expected {} but got {}".format(s, expected, output))
            assert not grading_mode
            return
    print("++ Success!")

test1()
test2()
test3()
test4()
test5()
