#lang forge

open "cellular-automata.frg"

--========================================================--
--  GARDENS OF EDENS                                      --
--========================================================--

// if test fails, firstState is a candidate GoE
// NOTE: this is a candidate GoE *given the bounds*
// NOTE2: comment out this section to run exclusion runs

rule30GoE: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule30step[pre, Board.firstState]
} is unsat for exactly 32 BoardState, 5 Int

// if test fails, firstState is a candidate GoE
rule90GoE: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule90step[pre, Board.firstState]
} is unsat for /*exactly 32 BoardState,*/ 5 Int

rule110GoE: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule110step[pre, Board.firstState]
} is unsat for /*exactly 32 BoardState,*/ 5 Int

rule184GoE: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule184step[pre, Board.firstState]
} is unsat for /*exactly 32 BoardState,*/ 5 Int

--========================================================--
--  GARDENS OF EDENS WITH CONSTRAINTS                     --
--========================================================--

// NOTE: comment out the section above to run these. Please note that you also have to comment out 
// other ruleXXGoE_blockedList run commands to run just a specific one as well.

pred notTranslationOf[s: BoardState, pattern: Int->Int] {
    no dx: Int | s.alive = { r: Int, c: Int | r=0 and (0->add[c, dx]) in pattern }
}

pred r30_excludedPatterns[s: BoardState] {
    -- known GoE
    notTranslationOf[s, (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-12) + (0->-11) + (0->-10) + (0->-9) + (0->-8) + (0->-7) + (0->-6) + (0->-5) + (0->-4) + (0->-3) + (0->-2) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->12) + (0->13) + (0->14) + (0->15)]

    -- known non GoE
    notTranslationOf[s, (0->-8) + (0->-4) + (0->0) + (0->1) + (0->2) + (0->3) + (0->6)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14) + (0->15)]
}

rule30GoE_blockedList: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule30step[pre, Board.firstState]
    r30_excludedPatterns[Board.firstState]
} is unsat for exactly 128 BoardState, 5 Int

pred twoOrThreeCellsTogether[s: BoardState] {
    some c: Int | {
        (0->c) in s.alive
        some left, right: Int | {
            left = add[c, 1]
            right = subtract[c, 1]
            (0->left) in s.alive or (0->right) in s.alive
        }
    }
}

pred r90_excludedPatterns[s: BoardState] {
    -- found GoE
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->14)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14)]
    // 2 cells together
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->14) + (0->15)]
    // 3 cells together
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14) + (0->15)]
    notTranslationOf[s, (0->-12) + (0->-10) + (0->-7) + (0->-4) + (0->-2) + (0->0) + (0->4) + (0->6) + (0->8) + (0->12) + (0->14)]
    not twoOrThreeCellsTogether[s]

    -- found non GoE
    // all cells apart from each other
    notTranslationOf[s, (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-12) + (0->-11) + (0->-10) + (0->-9) + (0->-8) + (0->-7) + (0->-6) + (0->-5) + (0->-4) + (0->-3) + (0->-2) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->12) + (0->13) + (0->14) + (0->15)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11)]
    notTranslationOf[s, (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->15)]
}

rule90GoE_blockedList: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule90step[pre, Board.firstState]
    r90_excludedPatterns[Board.firstState]
} is unsat for exactly 128 BoardState, 5 Int

verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule30step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14) + (0->15)
} is unsat for exactly 2 BoardState, 5 Int

--========================================================--
--  TWINS                                                 --
--========================================================--

// NOTE: again, boundedness issues might not necessarily mean its a twin
// the boundedness issue here is that it's not certain that every configuration with
// these subsets necessarily generates the same next state

// NOTE2: comment out Gardens of Edens with Constraints section to let this section run.

r30_findTwin: assert {
    board1D

    some disj s1, s2: BoardState | {
        s1 = Board.firstState
        some s1.alive
        some s2.alive
        s1.alive != s2.alive
        strong_twin_r30[s1, s2]
    }
} is unsat for exactly 4 BoardState, 5 Int

// NOTE: verification is not sound either unfortunately for the same reason
r30_verifyTwin: assert {
    board1D

    // twin 1
    Board.firstState.alive = (0->-6) + (0->-2)
    // twin 2
    some s: BoardState | {
        s.alive = (0->-8) + (0->-5) + (0->-4) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7)
        strong_twin_r30[Board.firstState, s]
    }
} is sat for exactly 4 BoardState, 5 Int
