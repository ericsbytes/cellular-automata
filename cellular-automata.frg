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

// can reach s2 from s1
pred reachable[s1, s2: BoardState] {
    s2 in s1.^(Board.next)
}å


// thanks tim
fun neighborhoods[alyv: Int->Int]: Int->Int->Int->Int {
    { r: Int, c: Int, r2: Int, c2: Int |
        let rows = (add[r, 1] + r + add[r, -1]) |
        let cols = (add[c, 1] + c + add[c, -1]) |
            (r2->c2) in (alyv & ((rows->cols) - (r->c))) }
}

pred step {
    all curr: BoardState | some Board.next[curr] implies {
        let nhood = neighborhoods[curr.alive] |
            // A cell becomes alive if it had 3 cells in the previous state.
            let birthing =  { r: Int, c: Int | (r->c) not in curr.alive and #nhood[r][c] in 3 } |
            // A cell survives if it had 2 or 3 neighbors in a previous state.
            let surviving = { r: Int, c: Int | (r->c) in curr.alive and #nhood[r][c] in (2 + 3) } |
                Board.next[curr].alive = birthing + surviving
    }
    
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

--========================================================--
--  RULES                                                 --
--========================================================--

fun rule30next[pre: BoardState]: set Int->Int {
    { 
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            ((0->left)  in pre.alive and (0->c) not in pre.alive and (0->right) not in pre.alive)
            or
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right)  in pre.alive)
            or
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right) not in pre.alive)
            or
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
        )
    }
}

pred rule30step[pre, post: BoardState] {
    post.alive = rule30next[pre]
}

fun rule90next[pre, post: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            ((0->left)  in pre.alive and (0->c)  in pre.alive and (0->right) not in pre.alive)
            or
            ((0->left)  in pre.alive and (0->c) not in pre.alive and (0->right) not in pre.alive)
            or
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right)  in pre.alive)
            or
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
        )
    }
}

pred rule90step[pre, post: BoardState] {
    post.alive = rule90next[pre]
}

fun rule110next[pre, post: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            ((0->left)  in pre.alive and (0->c)  in pre.alive and (0->right) not in pre.alive)
            or
            // 101 -> 1
            ((0->left)  in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
            or
            // 011 -> 1
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right)  in pre.alive)
            or
            // 010 -> 1
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right) not in pre.alive)
            or
            // 001 -> 1
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
        )
    }
}

pred rule110step[pre, post: BoardState] {
    post.alive = rule110next[pre]
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
--  TWINS                                                 --
--========================================================--

pred twin_r30[bs, other: BoardState] {
    all s1, s2: BoardState | {
        s2.alive = (s1.alive - bs.alive) + other.alive implies rule30next[s1] = rule30next[s2]
    }

    all s1, s2: BoardState | {
        s2.alive = (s1.alive - other.alive) + bs.alive implies rule30next[s1] = rule30next[s2]
    }
}

// NOTE: again, boundedness issues might not necessarily mean its a twin
findR30Twin: assert {
    board1D
    no disj s1, s2: BoardState | {
        some s1.alive
        some s2.alive
        s1.alive != s2.alive
        twin_r30[s1, s2]
    }
} is unsat for exactly 32 BoardState, 5 Int



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

// if test fails, firstState found a candidate GoE
rule90GoE: assert {
    board1D 
    some Board.firstState.alive
    no pre: BoardState | rule90step[pre, Board.firstState]
} is unsat for /*exactly 32 BoardState,*/ 5 Int


// possible expansions
// - given a configuration, attempt to verify if it's orphan or not
// - attempt to verify twins <=> orphans
// - verify that when a rule is not supposed to have orphans, it doesn't generate orphans
// - find more orphans by restricting boring configurations
// - bijective <=> twins

rule110findOrphan: run {
    wellformed
    board1D
    all s: BoardState | some Board.next[s] implies rule110step[s,  Board.next[s]]
    some s: BoardState | r110isOrphan[s]
} for exactly 5 BoardState, 4 Int

// should be unsat!! but generates instances
// probable explanation is that rule 90 is surjective in infinite grids, but because
// it is limited to a wrap-around board, it may not be surjective anymore
rule90GoE: run {
    wellformed
    board1D
    all s: BoardState | some Board.next[s] implies rule90step[s,  Board.next[s]]
    some Board.firstState.alive
    garden_of_eden_r90
} for exactly 3 BoardState, 5 Int

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
