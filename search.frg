#lang forge

open "cellular-automata.frg"

--========================================================--
--  GARDENS OF EDENS                                      --
--========================================================--

// if test fails, firstState is a candidate GoE
// NOTE: this is a candidate GoE *given the bounds*

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

--========================================================--
--  TWINS                                                 --
--========================================================--

// NOTE: again, boundedness issues might not necessarily mean its a twin
// the boundedness issue here is that it's not certain that every configuration with
// these subsets necessarily generates the same next state

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
