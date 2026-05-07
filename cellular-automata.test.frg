#lang forge

open "cellular-automata.frg"

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

test suite for rule110step {
    // example r110SmallestOrphan is {garden_of_eden_r110} for {
    //     // smallest known orphan is 01010
    //     Board = `Board0
    //     BoardState = `s0 + `s1 + `s2
    //     `Board0.firstState = `s0
    //     `Board0.next = `s0 -> `s1 + `s1 -> `s2
    //     `s0.alive = (0->1) + (0->3)
    //     `s1.alive = none->none
    //     `s2.alive = none->none
    // }

    
}
/*
r110_goeExists: assert { // might be buggy
    wellformed
    board1D
    r110linearity
    garden_of_eden_r110
} is sat for exactly 3 BoardState, 4 Int
*/

// r30_goeIffTwin: assert {
    
// }
/*
test suite for rule90step {
    r90_goeExists: assert {
        wellformed
        board1D
        r90linearity
        garden_of_eden_r90
    } is sat for exactly 3 BoardState, 4 Int

    // r90_all
}
*/
r110_verifyKnownOrphan: assert {
    wellformed
    board1D
    r110linearity
    some s: BoardState | {
        some orphan: BoardState | {
            s != orphan
            orphan.alive = (0->1) + (0->3)
            rule110step[s, orphan]
        }
    }
} is unsat for exactly 3 BoardState, 4 Int

// a rule 30 GoE
verifyGoE1: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule30step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-12) + (0->-11) + (0->-10) + (0->-9) + (0->-8) + (0->-7) + (0->-6) + (0->-5) + (0->-4) + (0->-3) + (0->-2) + (0->-1) + (0->0) + (0->1) + (0->2) + (0->3) + (0->4) + (0->5) + (0->6) + (0->7) + (0->8) + (0->9) + (0->10) + (0->11) + (0->12) + (0->13) + (0->14) + (0->15)
} is unsat for exactly 2 BoardState, 5 Int


// a rule 90 GoE
verifyGoE2: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-11) + (0->-10) + (0->-8) + (0->-7) + (0->-5) + (0->-4) + (0->-2) + (0->-1) + (0->1) + (0->2) + (0->4) + (0->5) + (0->7) + (0->8) + (0->10) + (0->11) + (0->13) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int

verifyGoE3: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14)
} is unsat for exactly 2 BoardState, 5 Int

verifyGoE4: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-8) + (0->-4) + (0->0) + (0->1) + (0->2) + (0->3) + (0->6)
} is unsat for exactly 2 BoardState, 5 Int


// a rule 90 GoE
verifyWrongGoE3: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule90step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-16) + (0->-15) + (0->-14) + (0->-13) + (0->-11) + (0->-10) + (0->-8)
} is unsat for exactly 2 BoardState, 5 Int

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

query: assert {
    board1D
    
    // change for rule
    some pre: BoardState | rule30step[pre, Board.firstState]
    
    // change pattern to verify GoE
    Board.firstState.alive = (0->-15) + (0->-13) + (0->-11) + (0->-9) + (0->-7) + (0->-5) + (0->-3) + (0->-1) + (0->1) + (0->3) + (0->5) + (0->7) + (0->9) + (0->11) + (0->13) + (0->14) + (0->15)
} is unsat for exactly 2 BoardState, 5 Int
