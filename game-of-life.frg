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
}

// can reach s2 from s1
pred reachable[s1, s2: BoardState] {
    s2 in s1.^(Board.next)
}

pred init {
    // we want init state to be something that forge simulates, not chosen by us right
}



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
pred twin[s1, s2: BoardState] {
    some dx, dy: Int | {
        s2.alive = { r: Int, c: Int | add[r, dx]->add[c, dy] in s1.alive }
    }
}


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

pred rule30step {
    all curr: BoardState | some Board.next[curr] implies {
        let n = Board.next[curr] | n.alive = { 
            r: Int, c: Int | r = 0 and 
                (
                    let left  = add[c, -1] |
                    let right = add[c,  1] |
                    -- 100 -> 1
                    ((0->left) in curr.alive and (0->c) not in curr.alive and (0->right) not in curr.alive)
                    or
                    -- 011 -> 1
                    ((0->left) not in curr.alive and (0->c) in curr.alive and (0->right) in curr.alive)
                    or
                    -- 010 -> 1
                    ((0->left) not in curr.alive and (0->c) in curr.alive and (0->right) not in curr.alive)
                    or
                    -- 001 -> 1
                    ((0->left) not in curr.alive and (0->c) not in curr.alive and (0->right) in curr.alive)
                )
        }
    }
}


pred rule90step {
    all curr: BoardState | some Board.next[curr] implies {
        let n = Board.next[curr] | n.alive = { 
            r: Int, c: Int | r = 0 and 
                (
                    let left  = add[c, -1] |
                    let right = add[c,  1] |
                    -- 110 -> 1
                    ((0->left) in curr.alive and (0->c) in curr.alive and (0->right) not in curr.alive)
                    or
                    -- 100 -> 1
                    ((0->left) in curr.alive and (0->c) not in curr.alive and (0->right) not in curr.alive)
                    or
                    -- 011 -> 1
                    ((0->left) not in curr.alive and (0->c) in curr.alive and (0->right) in curr.alive)
                    or
                    -- 001 -> 1
                    ((0->left) not in curr.alive and (0->c) not in curr.alive and (0->right) in curr.alive)
                )
        }
    }
}

pred trace {
    wellformed
    rule30step
    Board.firstState.alive = 0->7
    all r, c: Int | {
        c != 7 implies (r->c) not in Board.firstState.alive
    } 
}

OneDrule30: run {
    board1D
    trace
} for exactly 8 BoardState, 5 Int
