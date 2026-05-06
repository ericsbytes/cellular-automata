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

    r110_goeExists: assert { // might be buggy
        wellformed
        board1D
        r110linearity
        garden_of_eden_r110
    } is sat for exactly 3 BoardState, 4 Int
}

test suite for rule90step {
    
}