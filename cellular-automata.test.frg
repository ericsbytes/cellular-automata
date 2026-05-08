#lang forge

open "cellular-automata.frg"


--========================================================--
--  HELPER PREDICATES                                     --
--========================================================--

pred r30linearity {
    all disj s1, s2: BoardState | {
        Board.next[s1] = s2 implies rule30step[s1, s2]
    }
}

pred r90linearity {
    all disj s1, s2: BoardState | {
        Board.next[s1] = s2 implies rule90step[s1, s2]
    }
}

pred r110linearity {
    all disj s1, s2: BoardState | {
        Board.next[s1] = s2 implies rule110step[s1, s2]
    }
}


test_left_right_consistency: assert {
    board1D
    some c: Int | {
        left[c] = add[c, -1]
        right[c] = add[c, 1]
        left[right[c]] = c
        right[left[c]] = c
    }
} is sat for exactly 1 BoardState, 5 Int

test_leftState_definition: assert {
    board1D
    all s: BoardState | all c: Int | {
        leftState[s, c] iff (0->left[c]) in s.alive
    }
} is sat for exactly 2 BoardState, 5 Int

test_rightState_definition: assert {
    board1D
    all s: BoardState | all c: Int | {
        rightState[s, c] iff (0->right[c]) in s.alive
    }
} is sat for exactly 2 BoardState, 5 Int

test_state_predicates_consistency: assert {
    board1D
    all s: BoardState | all c: Int | {
        (leftState[s, c] and centerState[s, c] and rightState[s, c]) implies {
            (0->left[c]) in s.alive
            (0->c) in s.alive
            (0->right[c]) in s.alive
        }
    }
} is sat for exactly 2 BoardState, 5 Int


test suite for wellformed {
    -- Test 1: Disconnected states should violate wellformed
    GW_disconnected: assert {
        some s: BoardState | s not in Board.firstState.*(Board.next)
        wellformed
    } is unsat
    
    -- Test 2: Multiple last states should violate wellformed
    GW_moreThanOneLast: assert {
        wellformed
        some disj s1, s2: BoardState | {
            no Board.next[s1]
            no Board.next[s2]
        }
    } is unsat

    -- Test 3: Cycles should violate wellformed
    GW_cycle: assert {
        wellformed
        some s: BoardState | s in Board.next[s]
    } is unsat
    
    -- Test 4: First state having predecessor violates wellformed
    GW_firstHasPredecessor: assert {
        wellformed
        some s: BoardState | Board.next[s] = Board.firstState
    } is unsat

    GW_validTrace: assert {
        wellformed
        board1D
        Board.firstState.alive = 0->0
        all s: BoardState | some Board.next[s] implies rule30step[s, Board.next[s]]
    } is sat for exactly 4 BoardState, 5 Int
}

    test_board1D: assert {
        board1D
        some s: BoardState | some r, c: Int | {
            (r->c) in s.alive
            r != 0
        }
    } is unsat for exactly 2 BoardState, 5 Int
    
    -- Test board2D violation
    test_board2D_violation: assert {
        board2D[3, 3]
        some s: BoardState | some r, c: Int | {
            (r->c) in s.alive
            (r >= 3 or c >= 3)
        }
    } is unsat for exactly 2 BoardState, 5 Int


--========================================================--
--  Property tests                       --
--========================================================--

test_rule30_not_additive: assert {
    board1D
    all c: Int, s: BoardState | c < -5 or c >= 5 implies (0->c) not in s.alive
    
    some disj s1, s2, sXOR, r1, r2, rXOR: BoardState | {
        sXOR.alive = (s1.alive - s2.alive) + (s2.alive - s1.alive)
        rule30step[s1, r1]
        rule30step[s2, r2]
        rule30step[sXOR, rXOR]
        rXOR.alive != (r1.alive - r2.alive) + (r2.alive - r1.alive)
    }
} is sat for exactly 6 BoardState, 4 Int

test_rule60_additive: assert {
    board1D
    all c: Int, s: BoardState | c < -5 or c >= 5 implies (0->c) not in s.alive
    
    some disj s1, s2, sXOR, r1, r2, rXOR: BoardState | {
        sXOR.alive = (s1.alive - s2.alive) + (s2.alive - s1.alive)
        rule60step[s1, r1]
        rule60step[s2, r2]
        rule60step[sXOR, rXOR]
        rXOR.alive != (r1.alive - r2.alive) + (r2.alive - r1.alive)
    }
} is unsat for exactly 6 BoardState, 4 Int

test_rule110_not_injective: assert {
    board1D
    all c: Int, s: BoardState | c < -5 or c >= 5 implies (0->c) not in s.alive
    
    some s1, s2, r1, r2: BoardState | {
        s1 != s2
        rule110step[s1, r1]
        rule110step[s2, r2]
        r1.alive = r2.alive
    }
} is sat for exactly 4 BoardState, 4 Int

test_rule60_not_monotonic: assert {
    board1D
    all c: Int, s: BoardState | c < -5 or c >= 5 implies (0->c) not in s.alive
    
    some s1, s2, r1, r2: BoardState | {
        s1.alive in s2.alive
        rule60step[s1, r1]
        rule60step[s2, r2]
        not (r1.alive in r2.alive)
    }
} is sat for exactly 5 BoardState, 4 Int

test_rule170_monotonic: assert {
    board1D
    all c: Int, s: BoardState | c < -5 or c >= 5 implies (0->c) not in s.alive
    
    some s1, s2, r1, r2: BoardState | {
        s1.alive in s2.alive
        rule170step[s1, r1]
        rule170step[s2, r2]
        not (r1.alive in r2.alive)
    }
} is unsat for exactly 5 BoardState, 4 Int





--========================================================--
--  RULE SANITY CHECKS                                    --
--========================================================--

r30_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule30step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 110 -> 0
                (leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 101 -> 0
                (leftState[s1, c] and not centerState[s1, c] and rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r45_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule45step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 110 -> 0
                (leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 100 -> 0
                (leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c]) or
                // 001 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and rightState[s1, c])
            )
            (0->c) in s2.alive
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r60_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule60step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 110 -> 0
                (leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 001 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r67_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule67step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 101 -> 0
                (leftState[s1, c] and not centerState[s1, c] and rightState[s1, c]) or
                // 100 -> 0
                (leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c]) or
                // 011 -> 0
                (not leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 010 -> 0
                (not leftState[s1, c] and centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r73_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule73step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 101 -> 0
                (leftState[s1, c] and not centerState[s1, c] and rightState[s1, c]) or
                // 100 -> 0
                (leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c]) or
                // 010 -> 0
                (not leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 001 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r90_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule90step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 101 -> 0
                (leftState[s1, c] and not centerState[s1, c] and rightState[s1, c]) or
                // 010 -> 0
                (not leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r102_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule102step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 100 -> 0
                (leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c]) or
                // 011 -> 0
                (not leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r110_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule110step[s1, s2]

        some c: Int | {
            (
                // 111 -> 0
                (leftState[s1, c] and centerState[s1, c] and rightState[s1, c]) or
                // 100 -> 0
                (leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r170_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule170step[s1, s2]

        some c: Int | {
            (
                // 110 -> 0
                (leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 100 -> 0
                (leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c]) or
                // 010 -> 0
                (not leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

r184_shouldBeDead: assert {
    wellformed
    some disj s1, s2: BoardState | {
        rule184step[s1, s2]

        some c: Int | {
            (
                // 110 -> 0
                (leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 010 -> 0
                (not leftState[s1, c] and centerState[s1, c] and not rightState[s1, c]) or
                // 001 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and rightState[s1, c]) or
                // 000 -> 0
                (not leftState[s1, c] and not centerState[s1, c] and not rightState[s1, c])
            )
            (0->c) in s2.alive
            
        }
    }
} is unsat for exactly 2 BoardState, 5 Int

--========================================================--
--  VERIFY (KNOWN) GARDEN OF EDEN                         --
--========================================================--

// a rule 30 GoE
r30_verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule30step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-12) + (0->-11) + (0->-10) + (0->-9) + (0->-8) + (0->-7) + (0->-6) + (0->-5) + (0->-4) + (0->-3) + (0->-2) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->12) + (0->13) + (0->14) + (0->15)
} is unsat for exactly 2 BoardState, 5 Int

// a rule 90 GoE
r90_verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-11) + (0->-10) + (0->-8) + (0->-7) + (0->-5) + (0->-4) + (0->-2) + (0->-1) + (0->1) + (0->2) + (0->4) + (0->5) + (0->7) + (0->8) + (0->10) + (0->11) + (0->13) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int

r90_verifyGoE2: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int


r90_verifyGoE3: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-8) + (0->-4) + (0->0) + (0->1) + (0->2) + (0->3) + (0->6)
} is unsat for exactly 2 BoardState, 5 Int

// found goe through synthesis and verification
r90_verifyGOE4: assert {
    board1D

    some pre: BoardState | rule90step[pre, Board.firstState]

    Board.firstState.alive = (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int

r90_verifyGOE5: assert {
    board1D
    some pre: BoardState | rule90step[pre, Board.firstState]
    Board.firstState.alive = (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13)
} is unsat for exactly 2 BoardState, 5 Int

r110_verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule110step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->1) + (0->3)
} is unsat for exactly 2 BoardState, 5 Int

--========================================================--
--  VERIFY NON-GOE                                        --
--========================================================--

r30_verifyNonGoE: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule30step[pre, target]
        target.alive = (0->-4) + (0->-3) + (0->0) + (0->4)
    }
} is sat for exactly 2 BoardState, 5 Int 

r90_verifyNonGoE: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule90step[pre, target]
        target.alive = (0->-3) + (0->-2) + (0->2) + (0->3)
    }
} is sat for exactly 2 BoardState, 5 Int

r110_verifyNonGoE: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule110step[pre, target]
        target.alive = (0->-3) + (0->-2) + (0->2) + (0->3)
    }
} is sat for exactly 2 BoardState, 5 Int

r110_verifyNonGoE2: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule110step[pre, target]
        target.alive = (0->-5) + (0->-4) + (0->-2) + (0->-1) + (0->0) + (0->2) + (0->3) + (0->4) + (0->5)
    }
} is sat for exactly 2 BoardState, 5 Int

// just in case, test a goe
r110_verifyGoEHasNoPrev: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule110step[pre, target]
        target.alive = (0->1) + (0->3)
    }
} is unsat for exactly 2 BoardState, 5 Int

r184_verifyNonGoE: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule184step[pre, target]
        target.alive = (0->0) + (0->2) + (0->4)
    }
} is sat for exactly 2 BoardState, 5 Int

r45_verifyNonGoE: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule45step[pre, target]
        target.alive = (0->-2) + (0->-1) + (0->0) + (0->1)
    }
} is sat for exactly 2 BoardState, 5 Int

r67_verifyNonGoE: assert {
    wellformed
    // change for rule
    some disj pre, target: BoardState | {
        Board.next[pre] = target
        rule67step[pre, target]
        target.alive = (0->-2) + (0->-1) + (0->0) + (0->1)
    }
} is sat for exactly 2 BoardState, 5 Int

// find something that's not a garden of eden and plug it in, expect it to fail
// make it look for a valid predecessor
// MAKE SURE THIS ACTUALLY HAPPENS

// what if we learn something more general from the failure of a specific candidate ..? find 
// "what fundamental property is wrong with this bad example"?
// 

r30_verifyWeakTwins: assert {
    board1D

    some disj s1, s2: BoardState | {
        s1.alive = (0->-12) + (0->-11) + (0->-9) + (0->-6) + (0->-2) + (0->13)
        s2.alive = (0->-16) + (0->-15) + (0->-13) + (0->-8) + (0->-5) + (0->-4) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->14) + (0->15)
        rule30next[s1] = rule30next[s2]
    }
} is sat for 5 Int


--========================================================--

// NOTE: this was used for manual testing
// sat if it found a predecessor ot the goe candidate
query: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-12) + (0->-10) + (0->-7) + (0->-4) + (0->-2) + (0->0) + (0->4) + (0->6) + (0->8) + (0->12) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int
