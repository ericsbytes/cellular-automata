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

test suite for wellformed {
    GW_disconnected: assert {
        some s: BoardState | s not in Board.firstState.*(Board.next)
        wellformed
    } is unsat

    GW_moreThanOneLast: assert {
        wellformed
        some disj s1, s2: BoardState | {
            no Board.next[s1]
            no Board.next[s2]
        }
    } is unsat
}

// test suite for rule110step {
//     r110_invalidStep: assert {
//         some disj s1, s2: BoardState | {
//             rule110step[s1, s3]
//             s1.alive
//         }
//     }
    
// }

--========================================================--
--  VERIFY GARDEN OF EDEN                                 --
--========================================================--

// a rule 30 GoE
r30_verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule30step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-12) + (0->-11) + (0->-10) + (0->-9) + (0->-8) + (0->-7) + (0->-6) + (0->-5) + (0->-4) + (0->-3) + (0->-2) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->12) + (0->13) + (0->14) + (0->15)
} is unsat for exactly 2 BoardState, 5 Int

// r30_verifyNonGoECheck: assert {
//     board1D
    
//     // change for rule
//     some pre: BoardState | rule30step[pre, Board.firstState]

//     // change pattern to verify GoE
//     Board.firstState.alive = (0->-4) + (0->-3) + (0->0) + (0->4)
// } is sat for exactly 2 BoardState, 5 Int

// a rule 90 GoE
r90_verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-11) + (0->-10) + (0->-8) + (0->-7) + (0->-5) + (0->-4) + (0->-2) + (0->-1) + (0->1) + (0->2) + (0->4) + (0->5) + (0->7) + (0->8) + (0->10) + (0->11) + (0->13) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int

// r90_verifyNonGoECheck: assert {
//     board1D
    
//     // change for rule
//     some pre: BoardState | rule90step[pre, Board.firstState]

//     // change pattern to verify GoE
//     Board.firstState.alive = (0->-3) + (0->-2) + (0->2) + (0->3)
// } is sat for exactly 2 BoardState, 5 Int

r110_verifyGoE: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule110step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->1) + (0->3)
} is unsat for exactly 2 BoardState, 5 Int

// r110_verifyNonGoECheck: assert {
//     board1D
    
//     // change for rule
//     some pre: BoardState | rule90step[pre, Board.firstState]

//     // change pattern to verify GoE
//     Board.firstState.alive = (0->-3) + (0->-2) + (0->2) + (0->3)
// } is sat for exactly 2 BoardState, 5 Int

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
        target.alive = (0->-5) + (0->-4) + (0->-2) + (0->-1) + (0->0) + (0->2) + (0->3) + (0->4) + (0->5)
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

r30_verifyExactTwins: assert {
    board1D

    some disj s1, s2: BoardState | {
        s1.alive = (0->-12) + (0->-11) + (0->-9) + (0->-6) + (0->-2) + (0->13)
        s2.alive = (0->-16) + (0->-15) + (0->-13) + (0->-8) + (0->-5) + (0->-4) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->14) + (0->15)
        rule30next[s1] = rule30next[s2]
    }
} is sat for 5 Int