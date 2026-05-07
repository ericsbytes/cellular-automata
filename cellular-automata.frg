#lang forge

option run_sterling "visualizer.js"

sig BoardState {
    alive: set Int->Int
}

one sig Board {
    firstState: one BoardState,
    next: pfunc BoardState -> BoardState
}

--========================================================--
--  SETUP PREDICATES                                      --
--========================================================--

pred wellformed {
    // first state cannot be next of some other state
    Board.firstState not in BoardState.(Board.next)

    // last state is the only one without a next state
    one lastState: BoardState | no Board.next[lastState]

    // states are linear
    no s: BoardState | s in s.^(Board.next)

    // all states should be connected
    Board.firstState.*(Board.next) = BoardState

    // one dimensional
    board1D
}

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

fun rule90next[pre: BoardState]: set Int->Int {
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

fun rule110next[pre: BoardState]: set Int->Int {
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

fun rule184next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            // 111 -> 1
            ((0->left)  in pre.alive and (0->c)  in pre.alive and (0->right) not in pre.alive)
            or
            // 101 -> 1
            ((0->left)  in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
            or
            // 100 -> 1
            ((0->left) in pre.alive and (0->c) not in pre.alive and (0->right) not in pre.alive)
            or
            // 011 -> 1
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right) in pre.alive)
        )
    }
}

pred rule184step[pre, post: BoardState] {
    post.alive = rule184next[pre]
}

fun rule73next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            // 110 -> 1
            ((0->left)  in pre.alive and (0->c) in pre.alive and (0->right) not in pre.alive)
            or
            // 011 -> 1
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right) in pre.alive)
            or 
            // 000 -> 1
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) not in pre.alive)
        )
    }
}

pred rule73step[pre, post: BoardState] {
    post.alive = rule73next[pre]
}

fun rule45next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            // 101 -> 1
            ((0->left)  in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
            or
            // 011 -> 1
            ((0->left) not in pre.alive and (0->c)  in pre.alive and (0->right) in pre.alive)
            or 
            // 010 -> 1
            ((0->left) not in pre.alive and (0->c) in pre.alive and (0->right) not in pre.alive)
            or
            // 000 -> 1
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) not in pre.alive)
        )
    }
}

pred rule45step[pre, post: BoardState] {
    post.alive = rule45next[pre]
}

fun rule67next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            let left  = add[c, -1] |
            let right = add[c,  1] |
            // 110 -> 1
            ((0->left)  in pre.alive and (0->c) in pre.alive and (0->right) not in pre.alive)
            or
            // 001 -> 1
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) in pre.alive)
            or 
            // 000 -> 1
            ((0->left) not in pre.alive and (0->c) not in pre.alive and (0->right) not in pre.alive)
        )
    }
}

pred rule67step[pre, post: BoardState] {
    post.alive = rule67next[pre]
}

--========================================================--
--  TRACES                                                --
--========================================================--

// gives a trace that starts from a single cell at (0, 0)
pred trace {
    wellformed
    Board.firstState.alive = 0->0
    all r, c: Int | {
        c != 0 implies (r->c) not in Board.firstState.alive
    } 
}

r30Trace: run {
    all s: BoardState | some Board.next[s] implies rule30step[s,  Board.next[s]]
    trace
} for exactly 8 BoardState, 5 Int

r90Trace: run {
    all s: BoardState | some Board.next[s] implies rule90step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int 

r110Trace: run {
    all s: BoardState | some Board.next[s] implies rule110step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int

r184Trace: run {
    all s: BoardState | some Board.next[s] implies rule184step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int

r73Trace: run {
    all s: BoardState | some Board.next[s] implies rule73step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int

r67Trace: run {
    all s: BoardState | some Board.next[s] implies rule67step[s,  Board.next[s]]
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