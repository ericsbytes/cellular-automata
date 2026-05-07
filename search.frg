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
        twin_r30[s1, s2]
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
        twin_r30[Board.firstState, s]
    }
} is sat for exactly 4 BoardState, 5 Int
