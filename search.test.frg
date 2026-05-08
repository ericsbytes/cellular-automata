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
