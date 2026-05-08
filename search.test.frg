#lang forge

open "search.frg"
open "cellular-automata.frg"

test suite for notTranslationOf{
    test_same_pattern_translated: assert {
    board1D
    all c: Int, s: BoardState | c < -10 or c >= 10 implies (0->c) not in s.alive
    
    some s: BoardState | {
        let pattern = (0->0) + (0->1) + (0->2) {
            s.alive = (0->5) + (0->6) + (0->7)  
            not notTranslationOf[s, pattern]  
        }
    }
} is sat for exactly 1 BoardState, 5 Int

test_different_pattern: assert {
    board1D
    all c: Int, s: BoardState | c < -10 or c >= 10 implies (0->c) not in s.alive
    
    some s: BoardState | {
        let pattern = (0->0) + (0->1) + (0->2) {
            s.alive = (0->0) + (0->2) + (0->4)  
            notTranslationOf[s, pattern]
        }
    }
} is sat for exactly 1 BoardState, 5 Int

test_empty_pattern: assert {
    board1D
    some s: BoardState | {
        let pattern = none {
            s.alive = (0->0) + (0->1)
            notTranslationOf[s, pattern]  
        }
    }
} is sat for exactly 1 BoardState, 5 Int

}


test suite for twoOrThreeCellsTogether{
test_two_adjacent: assert {
    board1D
    some s: BoardState | {
        (0->0) in s.alive
        (0->1) in s.alive
        twoOrThreeCellsTogether[s]
    }
} is sat for exactly 1 BoardState, 5 Int


test_three_adjacent: assert {
    board1D
    some s: BoardState | {
        (0->0) in s.alive
        (0->1) in s.alive
        (0->2) in s.alive
        twoOrThreeCellsTogether[s]
    }
} is sat for exactly 1 BoardState, 5 Int

test_with_gap: assert {
    board1D
    some s: BoardState | {
        (0->0) in s.alive
        (0->2) in s.alive
        (0->4) in s.alive
        not twoOrThreeCellsTogether[s]
    }
} is sat for exactly 1 BoardState, 5 Int

test_single_cell: assert {
    board1D
    some s: BoardState | {
        (0->0) in s.alive
        no (0->1) in s.alive
        no (0->-1) in s.alive
        twoOrThreeCellsTogether[s]
    }
} is unsat for exactly 1 BoardState, 5 Int

test_all_isolated: assert {
    board1D
    some s: BoardState | {
        (0->0) in s.alive
        (0->2) in s.alive
        (0->4) in s.alive
        (0->6) in s.alive
        twoOrThreeCellsTogether[s]
    }
} is unsat for exactly 1 BoardState, 5 Int
}