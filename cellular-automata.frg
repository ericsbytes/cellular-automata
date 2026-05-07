#lang forge

option run_sterling "visualizer.js"

sig BoardState {
    alive: set Int->Int
}

one sig Board {
    firstState: one BoardState,
    next: pfunc BoardState -> BoardState
}

pred wellformed {
    // first state cannot be next of some other state
    Board.firstState not in BoardState.(Board.next)

    // last state is the only one without a next state
    one lastState: BoardState | no Board.next[lastState]

    // states are linear
    no s: BoardState | s in s.^(Board.next)

    // all states should be connected
    Board.firstState.*(Board.next) = BoardState

    board1D
}


// Checks if cell will be alive in next state:
// pred willBeAlive[curr: BoardState, next: BoardState, r: Int, c: Int] {
//     Board.next[curr] = next
//     (r->c) in next.alive
// }

// // Check if a cell will die.
// pred willDie[curr: BoardState, next: BoardState, r: Int, c: Int] {
//     Board.next[curr] = next
//     (r->c) in curr.alive and (r->c) not in next.alive
// }

// // Check if a cell will be born.
// pred willBeBorn[curr: BoardState, next: BoardState, r: Int, c: Int] {
//     Board.next[curr] = next
//     (r->c) not in curr.alive and (r->c) in next.alive
// }

// Checks if two states are twins



assert wellformed is sat

// possible functions or preds
// - get neighbors
// - if a cell will die in the next state (checking neighbors)
// - check twin
// - check reachability (orphan)

// Any live cell with fewer than two live neighbours dies, as if by underpopulation.
// Any live cell with two or three live neighbours lives on to the next generation.
// Any live cell with more than three live neighbours dies, as if by overpopulation.
// Any dead cell with exactly three live neighbours becomes a live cell, as if by reproduction.

pred board1D {
    all s: BoardState | {
        all r, c: Int | (r->c) in s.alive implies {
            r = 0
        }
    }
}

pred board2D[rowSize, colSize: Int] {
    all s: BoardState | {
        all r, c: Int | (r->c) in s.alive implies {
            r < rowSize
            c < colSize
        }
    }
}

// Helper function to get left and right neighbors
fun left[c: Int]: Int { add[c, -1] }
fun right[c: Int]: Int { add[c,  1] }

// Helper functions to get the state of the three cells in a neighborhood
pred leftState[pre: BoardState, c: Int] { (0->left[c]) in pre.alive }
pred centerState[pre: BoardState, c: Int] { (0->c) in pre.alive }
pred rightState[pre: BoardState, c: Int] { (0->right[c]) in pre.alive }

--========================================================--
--  RULES                                                 --
--========================================================--

fun rule30next[pre: BoardState]: set Int->Int {
    { 
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c]) or  // 100
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or      // 011
            (not leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or  // 010
            (not leftState[pre, c] and not centerState[pre, c] and rightState[pre, c])     // 001
        )
    }
}

pred rule30step[pre, post: BoardState] {
    post.alive = rule30next[pre]
}

fun rule90next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or     // 110
            (leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c]) or // 100
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 011
            (not leftState[pre, c] and not centerState[pre, c] and rightState[pre, c])    // 001
        )
    }
}

pred rule90step[pre, post: BoardState] {
    post.alive = rule90next[pre]
}

fun rule110next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or     // 110
            (leftState[pre, c] and not centerState[pre, c] and rightState[pre, c]) or     // 101
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 011
            (not leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or // 010
            (not leftState[pre, c] and not centerState[pre, c] and rightState[pre, c])    // 001
        )
    }
}


pred rule110step[pre, post: BoardState] {
    post.alive = rule110next[pre]
}

// RULE 60: Pascal's triangle modulo 2 (XOR with left neighbor only)
fun rule60next[pre: BoardState]: set Int->Int {
    { r: Int, c: Int | r = 0 and 
        (leftState[pre, c] xor centerState[pre, c])
    }
}

pred rule60step[pre, post: BoardState] {
    post.alive = rule60next[pre]
}

// RULE 102: Right-triangular rule (XOR with right neighbor only)
fun rule102next[pre: BoardState]: set Int->Int {
    { r: Int, c: Int | r = 0 and 
        (centerState[pre, c] xor rightState[pre, c])
    }
}

pred rule102step[pre, post: BoardState] {
    post.alive = rule102next[pre]
}

--========================================================--
--  TRACES                                                --
--========================================================--


pred trace {
    wellformed
    Board.firstState.alive = 0->7
    all r, c: Int | {
        c != 7 implies (r->c) not in Board.firstState.alive
    } 
}

OneDrule30: run {
    board1D
    all s: BoardState | some Board.next[s] implies rule30step[s,  Board.next[s]]
    trace
} for exactly 8 BoardState, 5 Int

OneDrule90: run {
    board1D
    all s: BoardState | some Board.next[s] implies rule90step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int 

OneDrule110: run {
    board1D
    all s: BoardState | some Board.next[s] implies rule110step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int

--========================================================--
--  Preds                                                 --
--========================================================--

//Provind additive rules
pred rule60_isAdditive {
    all s1, s2, sXOR, r1, r2, rXOR: BoardState | {
        // Define XOR of two states
        sXOR.alive = (s1.alive - s2.alive) + (s2.alive - s1.alive)
        
        rule60step[s1, r1]
        rule60step[s2, r2]
        rule60step[sXOR, rXOR]
        
        rXOR.alive = (r1.alive - r2.alive) + (r2.alive - r1.alive)
    }
}
fun negate[c: Int]: Int {
    0 - c
}

//Proving mirrored rules
pred rule102_isMirrorOf_rule60 {
    all s, mirrored, r60, r102: BoardState | {
        // Mirror configuration: swap left and right
        mirrored.alive = { r: Int, c: Int | (0->negate[c]) in s.alive }
        
        rule60step[s, r60]
        rule102step[mirrored, r102]
        
        // Mirror the rule 60 result should equal rule 102 result
        r102.alive = { r: Int, c: Int | (0->negate[c]) in r60.alive }
    }
}

--========================================================--
--  TWINS                                                 --
--========================================================--

pred weak_twins_rule30 {
    some disj s1, s2, r1, r2: BoardState | {
        rule30step[s1, r1]
        rule30step[s2, r2]
        s1.alive != s2.alive
        r1.alive = r2.alive
    }
}

pred weak_twins_rule60 {
    some disj s1, s2, r1, r2: BoardState | {
        rule60step[s1, r1]
        rule60step[s2, r2]
        s1.alive != s2.alive
        r1.alive = r2.alive
    }
}

pred strong_twin_r30[bs, other: BoardState] {
    all s1, s2: BoardState | {
        s2.alive = (s1.alive - bs.alive) + other.alive implies rule30next[s1] = rule30next[s2]
    }

    all s1, s2: BoardState | {
        s2.alive = (s1.alive - other.alive) + bs.alive implies rule30next[s1] = rule30next[s2]
    }
}

// NOTE: what is sound is finding "exact" twins
r30_findExactTwin: run {
    board1D
    some disj s1, s2: BoardState | {
        some s1.alive
        some s2.alive
        s1.alive != s2.alive
        rule30next[s1] = rule30next[s2]
    }
} for exactly 2 BoardState, 5 Int



--========================================================--
--  PROPERTY PREDICATES                                --
--========================================================--




--========================================================--
--  GARDENS OF EDENS                                      --
--========================================================--

/*
    NOTE: refactored. see search.frg
*/

// possible expansions
// - given a configuration, attempt to verify if it's orphan or not
// - attempt to verify twins <=> orphans
// - verify that when a rule is not supposed to have orphans, it doesn't generate orphans
// - find more orphans by restricting boring configurations
// - bijective <=> twins

// should be unsat!! but generates instances
// probable explanation is that rule 90 is surjective in infinite grids, but because
// it is limited to a wrap-around board, it may not be surjective anymore

/*
rule90GoE: run {
    wellformed
    board1D
    all s: BoardState | some Board.next[s] implies rule90step[s,  Board.next[s]]
    some Board.firstState.alive
    garden_of_eden_r90
} for exactly 3 BoardState, 5 Int

rule110findOrphan: run {
    wellformed
    board1D
    all s: BoardState | some Board.next[s] implies rule110step[s,  Board.next[s]]
    some s: BoardState | r110isOrphan[s]
} for exactly 5 BoardState, 4 Int


rule110GoE: run {
    wellformed
    board1D
    all s: BoardState | some Board.next[s] implies rule110step[s,  Board.next[s]]
    some Board.firstState.alive
    
    garden_of_eden_r110
}

pred r110isOrphan[s: BoardState] {
    no prev: BoardState | {
        prev != s
        rule110step[prev, s]
    }
    all r, c: Int | (r->c) in s.alive implies {
        some subset: BoardState | {
            subset.alive = s.alive - (r->c)
            some prev: BoardState | {
                prev != subset
                rule110step[prev, subset]
            }
        }
    }
}
*/