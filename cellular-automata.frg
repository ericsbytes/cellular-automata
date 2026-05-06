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

pred rule30step[pre, post: BoardState] {
    post.alive = {
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

pred rule90step[pre, post: BoardState] {
    post.alive = {
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

pred rule110step[pre, post: BoardState] {
    post.alive = {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            // 110 -> 1
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

pred garden_of_eden_r30 {
    no prev: BoardState | {
        prev != Board.firstState
        rule30step[prev, Board.firstState]
    }
}

pred garden_of_eden_r90 {
    no prev: BoardState | {
        prev != Board.firstState
        rule90step[prev, Board.firstState]
    }
}

pred garden_of_eden_r110 {
    no prev: BoardState | {
        prev != Board.firstState
        rule110step[prev, Board.firstState]
    }
}

pred twin[s1, s2: BoardState] {
    some dx, dy: Int | {
        s2.alive = { r: Int, c: Int | add[r, dx]->add[c, dy] in s1.alive }
    }
}

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

rule30GoE: run {
    wellformed
    board1D
    some Board.firstState.alive
    garden_of_eden_r30
} for exactly 3 BoardState, 5 Int

// should be unsat!!
rule90GoE: run {
    wellformed
    board1D
    some Board.firstState.alive
    garden_of_eden_r90
} for exactly 3 BoardState, 5 Int

// possible expansions
// - given a configuration, attempt to verify if it's orphan or not
// - attempt to verify twins <=> orphans
// - verify that when a rule is not supposed to have orphans, it doesn't generate orphans
// - find more orphans by restricting boring configurations
// - bijective <=> twins