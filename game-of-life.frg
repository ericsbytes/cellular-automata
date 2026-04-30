#lang forge

sig BoardState {
    alive: set Int->Int
}

one sig Board {
    firstState: one BoardState,
    next: pfunc BoardState -> BoardState
}

pred wellformed {
    all s: BoardState | {
        all r, c: Int | (r->c) in s.alive implies {
            r >= 0
            c >= 0
        }
    }

    all s: BoardState | s not in s.^(Board.next)
}

pred init {
    // we want init state to be something that forge simulates, not chosen by us right
}

pred trace {
    init
    
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
pred willBeAlive[curr: BoardState, next: BoardState, r: Int, c: Int] {
    Board.next[curr] = next
    (r->c) in next.alive
}

// Check if a cell will die.
pred willDie[curr: BoardState, next: BoardState, r: Int, c: Int] {
    Board.next[curr] = next
    (r->c) in curr.alive and (r->c) not in next.alive
}

// Check if a cell will be born.
pred willBeBorn[curr: BoardState, next: BoardState, r: Int, c: Int] {
    Board.next[curr] = next
    (r->c) not in curr.alive and (r->c) in next.alive
}

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